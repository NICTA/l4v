(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ADT_C
imports
  Schedule_C Retype_C Recycle_C
  "AInvs.BCorres2_AI"
begin


definition
  exec_C :: "(cstate, int, strictc_errortype) body \<Rightarrow>
             (cstate, int, strictc_errortype) com \<Rightarrow>
             (cstate,unit) nondet_monad"
where
  "exec_C \<Gamma> c \<equiv> \<lambda>s. ({()} \<times> {s'. \<Gamma> \<turnstile> \<langle>c,Normal s\<rangle> \<Rightarrow> Normal s'},
     \<exists>xs. xs \<notin> range Normal \<and> \<Gamma> \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> xs)"

definition
  ct_running_C :: "cstate \<Rightarrow> bool"
where
  "ct_running_C s \<equiv> let
    g = globals s;
    hp = clift (t_hrs_' g);
    ct = ksCurThread_' g
  in \<exists>tcb. hp ct = Some tcb \<and>
           tsType_CL (thread_state_lift (tcbState_C tcb)) = scast ThreadState_Running"

definition
  "handleHypervisorEvent_C = (CALL schedule();; CALL activateThread())"

context kernel_m
begin

definition
  "callKernel_C e \<equiv> case e of
    SyscallEvent n \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleSyscall(syscall_from_H n))
  | UnknownSyscall n \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleUnknownSyscall(of_nat n))
  | UserLevelFault w1 w2 \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleUserLevelFault(w1,w2))
  | Interrupt \<Rightarrow> exec_C \<Gamma> (Call handleInterruptEntry_'proc)
  | VMFaultEvent t \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleVMFaultEvent(vm_fault_type_from_H t))
  | HypervisorEvent t \<Rightarrow> exec_C \<Gamma> handleHypervisorEvent_C"

definition
  "callKernel_withFastpath_C e \<equiv>
   if e = SyscallEvent syscall.SysCall \<or> e = SyscallEvent syscall.SysReplyRecv
   then exec_C \<Gamma> (\<acute>cptr :== CALL getRegister(\<acute>ksCurThread, scast Kernel_C.capRegister);;
                  \<acute>msgInfo :== CALL getRegister(\<acute>ksCurThread, scast Kernel_C.msgInfoRegister);;
                   IF e = SyscallEvent syscall.SysCall
                   THEN CALL fastpath_call(\<acute>cptr, \<acute>msgInfo)
                   ELSE CALL fastpath_reply_recv(\<acute>cptr, \<acute>msgInfo) FI)
   else callKernel_C e"

definition
  setTCBContext_C :: "user_context_C \<Rightarrow> tcb_C ptr \<Rightarrow> (cstate,unit) nondet_monad"
where
  "setTCBContext_C ct thread \<equiv>
  exec_C \<Gamma> (\<acute>t_hrs :== hrs_mem_update (heap_update (
    Ptr &((Ptr &(thread\<rightarrow>[''tcbArch_C'']) :: (arch_tcb_C ptr))\<rightarrow>[''tcbContext_C''])) ct) \<acute>t_hrs)"

lemma Basic_sem_eq:
  "\<Gamma>\<turnstile>\<langle>Basic f,s\<rangle> \<Rightarrow> s' = ((\<exists>t. s = Normal t \<and> s' = Normal (f t)) \<or> (\<forall>t. s \<noteq> Normal t \<and> s' = s))"
  apply (rule iffI)
   apply (erule exec_elim_cases, simp_all)[1]
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (rule exec.Basic)
  apply clarsimp
  apply (cases s, auto)
  done

lemma setTCBContext_C_corres:
  "\<lbrakk> ccontext_relation tc tc'; t' = tcb_ptr_to_ctcb_ptr t \<rbrakk> \<Longrightarrow>
  corres_underlying rf_sr nf nf' dc (pspace_domain_valid and tcb_at' t) \<top>
    (threadSet (\<lambda>tcb. tcb \<lparr> tcbArch := atcbContextSet tc (tcbArch tcb)\<rparr>) t) (setTCBContext_C tc' t')"
  apply (simp add: setTCBContext_C_def exec_C_def Basic_sem_eq corres_underlying_def)
  apply clarsimp
  apply (simp add: threadSet_def bind_assoc split_def exec_gets)
  apply (frule (1) obj_at_cslift_tcb)
  apply clarsimp
  apply (frule getObject_eq [rotated -1], simp)
   apply (simp add: objBits_simps')
  apply (simp add: NonDetMonad.bind_def split_def)
  apply (rule bexI)
   prefer 2
   apply assumption
  apply simp
  apply (frule setObject_eq [rotated -1], simp)
    apply (simp add: objBits_simps')
   apply (simp add: objBits_simps)
  apply clarsimp
  apply (rule bexI)
   prefer 2
   apply assumption
  apply clarsimp
  apply (clarsimp simp: typ_heap_simps')
  apply (thin_tac "(a,b) \<in> fst t" for a b t)+
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def
                        carch_state_relation_def cmachine_state_relation_def
                        typ_heap_simps' update_tcb_map_tos)
  apply (simp add: map_to_ctes_upd_tcb_no_ctes map_to_tcbs_upd tcb_cte_cases_def
                   cvariable_relation_upd_const ko_at_projectKO_opt cteSizeBits_def)
  apply (simp add: cep_relations_drop_fun_upd)
  apply (apply_conjunct \<open>match conclusion in \<open>cready_queues_relation _ _ _\<close> \<Rightarrow>
         \<open>erule cready_queues_relation_not_queue_ptrs; rule ext; simp split: if_split\<close>\<close>)
  apply (drule ko_at_projectKO_opt)
  apply (erule (2) cmap_relation_upd_relI)
    apply (simp add: ctcb_relation_def carch_tcb_relation_def)
   apply assumption
  apply simp
  done

end

definition
  "register_to_H \<equiv> inv register_from_H"

definition (in state_rel)
  to_user_context_C :: "user_context \<Rightarrow> user_context_C"
where
  "to_user_context_C uc \<equiv>
  user_context_C (ARRAY r. user_regs uc (register_to_H (of_nat r)))"

lemma (in kernel_m) ccontext_rel_to_C:
  "ccontext_relation uc (to_user_context_C uc)"
  unfolding ccontext_relation_def to_user_context_C_def cregs_relation_def
  by (clarsimp simp: register_to_H_def inv_def)

context state_rel begin

definition
  from_user_context_C :: "user_context_C \<Rightarrow> user_context"
where
  "from_user_context_C uc \<equiv>
  UserContext (\<lambda>r. (registers_C uc).[unat (register_from_H r)])"

definition
  getContext_C :: "tcb_C ptr \<Rightarrow> cstate \<Rightarrow> user_context"
where
  "getContext_C thread \<equiv>
   \<lambda>s. from_user_context_C (tcbContext_C (the (clift (t_hrs_' (globals s)) (Ptr &(thread\<rightarrow>[''tcbArch_C''])))))"

lemma from_user_context_C:
  "ccontext_relation uc uc' \<Longrightarrow> from_user_context_C uc' = uc"
  unfolding ccontext_relation_def cregs_relation_def
  by (cases uc) (auto simp: from_user_context_C_def)

end

context kernel_m begin

definition
  kernelEntry_C ::
    "bool \<Rightarrow> event \<Rightarrow> user_context \<Rightarrow> (cstate, user_context) nondet_monad"
  where
  "kernelEntry_C fp e tc \<equiv> do
    t \<leftarrow> gets (ksCurThread_' o globals);
    setTCBContext_C (to_user_context_C tc) t;
    if fp then callKernel_withFastpath_C e else callKernel_C e;
    t \<leftarrow> gets (ksCurThread_' o globals);
    gets $ getContext_C t
  od"

definition
  "kernel_call_C fp e \<equiv>
  {(s, m, s'). s' \<in> fst (split (kernelEntry_C fp e) s) \<and>
               m = (if ct_running_C (snd s') then UserMode else IdleMode)
             \<or> snd (split (kernelEntry_C fp e) s)}"

definition
  "getActiveIRQ_C \<equiv> exec_C \<Gamma> (Call getActiveIRQ_'proc)"

definition
  checkActiveIRQ_C :: "(cstate, bool) nondet_monad"
  where
  "checkActiveIRQ_C \<equiv>
   do getActiveIRQ_C;
      irq \<leftarrow> gets ret__unsigned_long_';
      return (irq \<noteq> scast irqInvalid)
   od"

definition
  check_active_irq_C :: "((user_context \<times> cstate) \<times> bool \<times> (user_context \<times> cstate)) set"
  where
  "check_active_irq_C \<equiv> {((tc, s), irq_raised, (tc, s')). (irq_raised, s') \<in> fst (checkActiveIRQ_C s)}"

end

(*Restrict our undefined initial state to only use the nondeterministic state*)
consts
  Init_C' :: "unit observable \<Rightarrow> cstate global_state set"

context begin interpretation Arch . (*FIXME: arch_split*)

definition "Init_C \<equiv> \<lambda>((tc,s),m,e). Init_C' ((tc, truncate_state s),m,e)"

definition
  user_mem_C :: "globals \<Rightarrow> machine_word \<Rightarrow> word8 option"
where
  "user_mem_C s \<equiv> \<lambda>p.
  case clift (t_hrs_' s) (Ptr (p && ~~mask pageBits)) of
    Some v \<Rightarrow> let off = p && mask pageBits >> word_size_bits;
                  w = index (user_data_C.words_C v) (unat off);
                  i = 7 - unat (p && mask word_size_bits);
                  bs = (word_rsplit w :: word8 list)
              in Some (bs!i)
  | None \<Rightarrow> None"


definition
  device_mem_C :: "globals \<Rightarrow> machine_word \<Rightarrow> machine_word option"
where
  "device_mem_C s \<equiv> \<lambda>p.
  case clift (t_hrs_' s) (Ptr (p && ~~mask pageBits)) of
    Some (v::user_data_device_C) \<Rightarrow> Some p
  | None \<Rightarrow> None"


(* FIXME: move to somewhere sensible *)
definition
  "setUserMem_C um \<equiv>
   modify (\<lambda>s. s\<lparr>globals := (globals s)\<lparr>t_hrs_' :=
     (%p. case um p of None \<Rightarrow> fst (t_hrs_' (globals s)) p | Some x \<Rightarrow> x,
      snd (t_hrs_' (globals s))) \<rparr>\<rparr>)"

definition
  "setDeviceState_C um \<equiv>
   modify (\<lambda>s. s\<lparr>globals := globals s\<lparr>phantom_machine_state_' := (phantom_machine_state_' (globals s))\<lparr>device_state := ((device_state (phantom_machine_state_' (globals s))) ++ um)\<rparr>\<rparr>\<rparr>)"

lemma setUserMem_C_def_foldl:
  "setUserMem_C um \<equiv>
   modify (\<lambda>s. s\<lparr>globals := (globals s)\<lparr>t_hrs_' :=
     (foldl (%f p. f(p := the (um p))) (fst (t_hrs_' (globals s)))
            (filter (%p. p : dom um) enum),
      snd (t_hrs_' (globals s))) \<rparr>\<rparr>)"
  apply (rule eq_reflection)
  apply (simp add: setUserMem_C_def)
  apply (rule arg_cong[where f=modify])
  apply (rule ext)
  apply (rule_tac f=globals_update in arg_cong2)
   apply (rule ext)
   apply (rule_tac f=t_hrs_'_update in arg_cong2)
    apply (rule ext)
    apply simp_all
  apply (rule ext)
  apply (simp add: foldl_fun_upd_value)
  apply (intro conjI impI)
   apply clarsimp
  apply (clarsimp split: option.splits)
  done

(* FIXME: move *_to_H to StateRelation_C.thy? *)
definition
  "cscheduler_action_to_H p \<equiv>
   if p = NULL then ResumeCurrentThread
   else if p = Ptr 1 then ChooseNewThread
   else SwitchToThread (ctcb_ptr_to_tcb_ptr p)"


declare max_word_not_0[simp]

lemma csch_act_rel_to_H:
  "(\<forall>t. a = SwitchToThread t \<longrightarrow> is_aligned t tcbBlockSizeBits) \<Longrightarrow>
   cscheduler_action_relation a p \<longleftrightarrow> cscheduler_action_to_H p = a"
  apply (cases a)
    apply (simp_all add: cscheduler_action_relation_def
                         cscheduler_action_to_H_def)
  apply safe
     apply (simp_all add: tcb_ptr_to_ctcb_ptr_def ctcb_ptr_to_tcb_ptr_def
                          ctcb_offset_defs is_aligned_mask mask_def max_word_def
                          objBits_defs)
  subgoal by word_bitwise simp
  by word_bitwise simp

definition
  cirqstate_to_H :: "machine_word \<Rightarrow> irqstate"
where
  "cirqstate_to_H w \<equiv>
   if w = scast Kernel_C.IRQSignal then irqstate.IRQSignal
   else if w = scast Kernel_C.IRQTimer then irqstate.IRQTimer
   else if w = scast Kernel_C.IRQInactive then irqstate.IRQInactive
   else irqstate.IRQReserved"

lemma cirqstate_cancel:
  "cirqstate_to_H \<circ> irqstate_to_C = id"
  apply (rule ext)
  apply (case_tac x)
  apply (auto simp: cirqstate_to_H_def Kernel_C.IRQInactive_def
                    Kernel_C.IRQTimer_def Kernel_C.IRQSignal_def
                    Kernel_C.IRQReserved_def)
  done

definition
  "cint_state_to_H cnode cirqs \<equiv>
   InterruptState (ptr_val cnode)
     (\<lambda>i::6 word. if i \<le> scast RISCV64.maxIRQ then cirqstate_to_H (index cirqs (unat i))
                else irqstate.IRQInactive)"

lemma cint_rel_to_H:
  "irqs_masked' s \<Longrightarrow>
   cinterrupt_relation (ksInterruptState s) n t \<Longrightarrow>
   cint_state_to_H n t = (ksInterruptState s)"
  apply (simp add: irqs_masked'_def)
  apply (cases "ksInterruptState s")
  apply (rename_tac "fun")
  apply (clarsimp simp: cinterrupt_relation_def cint_state_to_H_def
                        RISCV64.maxIRQ_def Kernel_C.maxIRQ_def)
  apply (rule ext)
  apply clarsimp
  apply (drule spec, erule impE, assumption)
  apply (drule_tac s="irqstate_to_C (fun i)" in sym,
         simp add: cirqstate_cancel[THEN fun_cong, simplified])
  done

definition
  "cstate_to_machine_H s \<equiv>
   (phantom_machine_state_' s)\<lparr>underlying_memory := option_to_0 \<circ> (user_mem_C s)\<rparr>"

lemma projectKO_opt_UserData [simp]:
  "projectKO_opt KOUserData = Some UserData"
  by (simp add: projectKO_opts_defs)

lemma ucast_ucast_mask_pageBits_shift:
  "ucast (ucast (p && mask pageBits >> 3) :: 9 word) = p && mask pageBits >> 3"
  apply (rule word_eqI)
  apply (auto simp: word_size nth_ucast nth_shiftr pageBits_def)
  done

definition
  "processMemory s \<equiv> (ksMachineState s) \<lparr>underlying_memory := option_to_0 \<circ> (user_mem' s)\<rparr>"

lemma unat_ucast_mask_pageBits_shift:
  "unat (ucast (p && mask pageBits >> 3) :: 9 word) = unat ((p::word64) && mask pageBits >> 3)"
  apply (simp only: unat_ucast)
  apply (rule Divides.mod_less, simp)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (rule shiftr_less_t2n)
  apply (rule order_le_less_trans [OF word_and_le1])
  apply (simp add: pageBits_def mask_def)
  done

lemma mask_pageBits_shift_sum:
  "unat n = unat (p && mask 3) \<Longrightarrow>
  (p && ~~ mask pageBits) + (p && mask pageBits >> 3) * 8 + n = (p::machine_word)"
  apply (clarsimp simp: ArchMove_C.word_shift_by_3)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
   apply arith
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size pageBits_def nth_shiftl nth_shiftr word_ops_nth_size)
  apply (auto simp: linorder_not_less SucSucMinus)
  done

lemma user_mem_C_relation:
  "\<lbrakk>cpspace_user_data_relation (ksPSpace s')
      (underlying_memory (ksMachineState s')) (t_hrs_' s);
    pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> user_mem_C s = user_mem' s'"
  apply (rule ext)
  apply (rename_tac p)
  apply (clarsimp simp: user_mem_C_def user_mem'_def
                  split: if_splits option.splits)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: pointerInUserData_def)
   apply (drule user_data_at_ko)
   apply (clarsimp simp: cmap_relation_def)
   apply (subgoal_tac "(Ptr (p && ~~mask pageBits) :: user_data_C ptr) \<in>
                        Ptr ` dom (heap_to_user_data (ksPSpace s') (underlying_memory (ksMachineState s')))")
    apply simp
    apply clarsimp
   apply (thin_tac "Ball A P" for A P)
   apply (thin_tac "t = dom (clift (t_hrs_' s))" for t)
   apply (rule imageI)
   apply (clarsimp simp: dom_def heap_to_user_data_def obj_at'_def projectKOs)
  apply (clarsimp simp: pointerInUserData_def)
  apply (clarsimp simp: cmap_relation_def)
  apply (drule equalityD2)
  apply (drule subsetD)
   apply (fastforce simp: dom_def)
  apply clarsimp
  apply (drule bspec)
   apply (fastforce simp: dom_def)
  apply (clarsimp simp: heap_to_user_data_def map_comp_def projectKOs
                  split: option.splits)
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: typ_at'_def ko_wp_at'_def objBitsKO_def)
   apply (drule pspace_distinctD')
    apply fastforce
   apply (clarsimp simp: objBitsKO_def)
  apply clarsimp
  apply (clarsimp simp: cuser_user_data_relation_def byte_to_word_heap_def Let_def)
  apply (erule_tac x="ucast (p && mask pageBits >> 3)" in allE)
  apply (simp add: ucast_ucast_mask_pageBits_shift unat_ucast_mask_pageBits_shift)
  apply (rotate_tac -1)
  apply (drule sym)
  apply (simp add: word_rsplit_rcat_size word_size word_size_bits_def)
  apply (case_tac "unat (p && mask 3)")
   apply (simp add: mask_pageBits_shift_sum [where n=0, simplified])
  apply (case_tac "nat")
   apply (simp add: mask_pageBits_shift_sum [where n=1, simplified])
  apply (case_tac "nata")
   apply (simp add: mask_pageBits_shift_sum [where n=2, simplified])
  apply (case_tac "natb")
   apply (simp add: mask_pageBits_shift_sum [where n=3, simplified])
  apply (case_tac "natc")
   apply (simp add: mask_pageBits_shift_sum [where n=4, simplified])
  apply (case_tac "natd")
   apply (simp add: mask_pageBits_shift_sum [where n=5, simplified])
  apply (case_tac "nate")
   apply (simp add: mask_pageBits_shift_sum [where n=6, simplified])
  apply (case_tac "natf")
   apply (simp add: mask_pageBits_shift_sum [where n=7, simplified])
  apply clarsimp
  apply (subgoal_tac "unat (p && mask 3) < unat (2^3::machine_word)")
   apply simp
  apply (fold word_less_nat_alt)
  apply (rule and_mask_less_size)
  apply (clarsimp simp: word_size)
  done


lemma device_mem_C_relation:
  "\<lbrakk>cpspace_device_data_relation (ksPSpace s')
      (underlying_memory (ksMachineState s')) (t_hrs_' s);
    pspace_distinct' s'\<rbrakk>
   \<Longrightarrow> device_mem_C s = device_mem' s'"
  apply (rule ext)
  apply (rename_tac p)
  apply (clarsimp simp: device_mem_C_def device_mem'_def
                  split: if_splits option.splits)
  apply (rule conjI)
   apply (clarsimp simp: pointerInDeviceData_def)
   apply (clarsimp simp: cmap_relation_def)
   apply (subgoal_tac "(Ptr (p && ~~mask pageBits) :: user_data_device_C ptr) \<in>
                        Ptr ` dom (heap_to_device_data (ksPSpace s') (underlying_memory (ksMachineState s')))")
    apply clarsimp
   apply (thin_tac "Ball A P" for A P)
   apply (thin_tac "t = dom (clift (t_hrs_' s))" for t)
   apply (drule device_data_at_ko)
   apply (rule imageI)
   apply (clarsimp simp: dom_def heap_to_device_data_def obj_at'_def projectKOs)
  apply (clarsimp simp: pointerInDeviceData_def)
  apply (clarsimp simp: cmap_relation_def)
  apply (drule equalityD2)
  apply (drule subsetD)
   apply (fastforce simp: dom_def)
  apply clarsimp
  apply (drule bspec)
   apply (fastforce simp: dom_def)
  apply (clarsimp simp: heap_to_device_data_def map_comp_def projectKOs
                  split: option.splits)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def objBitsKO_def)
  apply (drule pspace_distinctD')
  apply fastforce
  apply (clarsimp simp: objBitsKO_def)
  done

lemma
  assumes vms': "valid_machine_state' a"
  assumes mach_rel: "cmachine_state_relation (ksMachineState a) s"
  assumes um_rel:
    "cpspace_user_data_relation (ksPSpace a)
       (underlying_memory (ksMachineState a)) (t_hrs_' s)"
    "pspace_distinct' a"
  shows cstate_to_machine_H_correct: "cstate_to_machine_H s = observable_memory (ksMachineState a) (user_mem' a)"
proof -
  have "underlying_memory (observable_memory (ksMachineState a) (user_mem' a)) = option_to_0 \<circ> user_mem' a"
    apply (rule ext)
    using vms'[simplified valid_machine_state'_def]
    apply (auto simp: user_mem'_def option_to_0_def typ_at'_def ko_wp_at'_def
      option_to_ptr_def pointerInUserData_def observable_memory_def
            split: option.splits if_split_asm)
    done
  with mach_rel[simplified cmachine_state_relation_def]
       user_mem_C_relation[OF um_rel]
  show ?thesis
 apply (simp add: cstate_to_machine_H_def)
 apply (intro MachineTypes.machine_state.equality,simp_all add:observable_memory_def)
 done
qed


definition
  "array_to_map n c \<equiv> \<lambda>i. if i\<le>n then Some (index c (unat i)) else None"
lemma array_relation_to_map:
  "array_relation r n a c \<Longrightarrow> \<forall>i\<le>n. r (a i) (the (array_to_map n c i))"
  by (simp add: array_relation_def array_to_map_def)

lemma dom_array_to_map[simp]: "dom (array_to_map n c) = {i. i\<le>n}"
  by (simp add: array_to_map_def dom_def)
lemma ran_array_to_map:
  "ran (array_to_map n c) = {y. \<exists>i\<le>n. index c (unat i) = y}"
  by (auto simp: array_to_map_def ran_def Collect_eq)

text \<open>Note: Sometimes, @{text array_map_conv} might be more convenient
              in conjunction with @{const array_relation}.\<close>
definition "array_map_conv f n c \<equiv> map_comp f (array_to_map n c)"

lemma array_map_conv_def2:
  "array_map_conv f n c \<equiv> \<lambda>i. if i\<le>n then f (index c (unat i)) else None"
  by (rule eq_reflection, rule ext) (simp add: array_map_conv_def map_comp_def
                                               array_to_map_def)
lemma array_relation_map_conv:
  "array_relation r n a c \<Longrightarrow> \<forall>x y. r y x \<longrightarrow> (f x) = y \<Longrightarrow>
   \<forall>i>n. a i = None \<Longrightarrow> array_map_conv f n c = a"
  by (rule ext) (simp add: array_relation_def array_map_conv_def2)
lemma array_relation_map_conv2:
  "array_relation r n a c \<Longrightarrow> \<forall>x. \<forall>y\<in>range a. r y x \<longrightarrow> (f x) = y \<Longrightarrow>
   \<forall>i>n. a i = None \<Longrightarrow> array_map_conv f n c = a"
  by (rule ext) (simp add: array_relation_def array_map_conv_def2)
lemma array_map_conv_Some[simp]: "array_map_conv Some n c = array_to_map n c"
  by (simp add: array_map_conv_def map_comp_def)
lemma map_comp_array_map_conv_comm:
 "map_comp f (array_map_conv g n c) = array_map_conv (map_comp f g) n c"
  by (rule ext) (simp add: array_map_conv_def2 map_option_def map_comp_def)
lemma ran_array_map_conv:
  "ran (array_map_conv f n c) = {y. \<exists>i\<le>n. f (index c (unat i)) = Some y}"
  by (auto simp add: array_map_conv_def2 ran_def Collect_eq)

lemmas word_le_p2m1 = word_up_bound[of w for w]

end

context state_rel begin

definition
  "carch_state_to_H cstate \<equiv>
   RISCVKernelState
      (array_map_conv (\<lambda>x. if x=NULL then None else Some (ptr_val x))
                      (2^asid_high_bits - 1) (riscvKSASIDTable_' cstate))
      (\<lambda>level. if level = maxPTLevel then [symbol_table ''kernel_root_pageTable''] else [])
      riscvKSKernelVSpace_C"


lemma eq_option_to_ptr_rev:
  "Some 0 \<notin> A \<Longrightarrow>
   \<forall>x. \<forall>y\<in>A. ((=) \<circ> option_to_ptr) y x \<longrightarrow>
              (if x=NULL then None else Some (ptr_val x)) = y"
  by (force simp: option_to_ptr_def option_to_0_def split: option.splits)

lemma carch_state_to_H_correct:
  assumes valid:  "valid_arch_state' astate"
  assumes rel:    "carch_state_relation (ksArchState astate) (cstate)"
  shows           "carch_state_to_H cstate = ksArchState astate"
  apply (case_tac "ksArchState astate", simp)
  apply (rename_tac v1 v2 v3)
  using rel[simplified carch_state_relation_def carch_globals_def]
  apply (clarsimp simp: carch_state_to_H_def)
  apply (rule conjI)
  apply (rule array_relation_map_conv2[OF _ eq_option_to_ptr_rev])
    apply assumption
   using valid[simplified valid_arch_state'_def]
   apply (fastforce simp: valid_asid_table'_def)
  using valid[simplified valid_arch_state'_def]
  apply (clarsimp simp: valid_asid_table'_def mask_2pm1)
  apply fastforce
  sorry (* FIXME RISCV current definition of carch_state_to_H is not right, and valid_arch_state'
           is not sufficient to state a good one

apply (clarsimp simp: riscvKSGlobalPT_def)
apply (rule ext)
apply (clarsimp split: if_split)
apply (fastforce split: if_splits)

  apply (simp add: ccr3_relation_def split: cr3.splits)
  apply (rule conjI)
   prefer 2
   apply (rule ext)
   apply (clarsimp simp: x64_irq_state_relation_def array_relation_def array_map_conv_def
                         array_to_map_def)
   using valid[simplified valid_arch_state'_def valid_x64_irq_state'_def]
   apply (case_tac "x \<le> maxIRQ"; fastforce split: option.split)
  apply (clarsimp simp: global_ioport_bitmap_relation_def)
  done
  *)

end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma tcb_queue_rel_unique:
  "hp NULL = None \<Longrightarrow>
   tcb_queue_relation gn gp' hp as pp cp \<Longrightarrow>
   tcb_queue_relation gn gp' hp as' pp cp \<Longrightarrow> as' = as"
proof (induct as arbitrary: as' pp cp)
  case Nil thus ?case by (cases as', simp+)
next
  case (Cons x xs) thus ?case
    by (cases as') (clarsimp simp: tcb_ptr_to_ctcb_ptr_def)+
qed

lemma tcb_queue_rel'_unique:
  "hp NULL = None \<Longrightarrow>
   tcb_queue_relation' gn gp' hp as pp cp \<Longrightarrow>
   tcb_queue_relation' gn gp' hp as' pp cp \<Longrightarrow> as' = as"
  apply (clarsimp simp: tcb_queue_relation'_def split: if_split_asm)
    apply (clarsimp simp: neq_Nil_conv)
   apply (clarsimp simp: neq_Nil_conv)
  apply (erule(2) tcb_queue_rel_unique)
  done

definition
  cready_queues_to_H
  :: "(tcb_C ptr \<rightharpoonup> tcb_C) \<Rightarrow> (tcb_queue_C[4096]) \<Rightarrow> word8 \<times> word8 \<Rightarrow> machine_word list"
  where
  "cready_queues_to_H h_tcb cs \<equiv> \<lambda>(qdom, prio). if ucast minDom \<le> qdom \<and> qdom \<le> ucast maxDom
              \<and> ucast seL4_MinPrio \<le> prio \<and> prio \<le> ucast seL4_MaxPrio
   then THE aq. let cqueue = index cs (cready_queues_index_to_C qdom prio)
    in sched_queue_relation' h_tcb aq (head_C cqueue) (StateRelation_C.end_C cqueue)
   else []"

lemma cready_queues_to_H_correct:
  "cready_queues_relation (clift s) cs as \<Longrightarrow>
   cready_queues_to_H (clift s) cs = as"
  apply (clarsimp simp: cready_queues_to_H_def cready_queues_relation_def
                   fun_eq_iff)
  apply (rule the_equality)
   apply simp
  apply (clarsimp simp: Let_def)
  apply (rule_tac hp="clift s" in tcb_queue_rel'_unique, simp_all add: lift_t_NULL)
  done

(* showing that cpspace_relation is actually unique >>>*)

lemma cmap_relation_unique_0:
  assumes inj_f: "inj f"
  assumes r: "\<And>x y z p . \<lbrakk> r x z; r y z; a p = Some x; a' p = Some y; P p x; P' p y \<rbrakk> \<Longrightarrow> x=y"
  shows "\<lbrakk> cmap_relation a c f r; cmap_relation a' c f r;
           \<forall>p x. a p = Some x \<longrightarrow> P p x; \<forall>p x. a' p = Some x \<longrightarrow> P' p x \<rbrakk> \<Longrightarrow> a' = a"
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_f])+
  apply simp
  apply (rule ext)
  apply (case_tac "x:dom a")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   apply (drule (1) r)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply (thin_tac "inv f ` A = B" for A B)
   apply (thin_tac "\<forall>p x. a p = Some x \<longrightarrow> P p x" for a P)
   apply (thin_tac "\<forall>x. a p = Some x \<longrightarrow> P p x" for a P p)
   apply (erule_tac x=x in allE)
   apply clarsimp
  apply (thin_tac "\<forall>p x. a p = Some x \<longrightarrow> P p x" for a P)+
  apply fastforce
  done

lemma cmap_relation_unique':
  assumes inj_f: "inj f"
  assumes r: "\<And>x y z. r x z \<Longrightarrow> r y z \<Longrightarrow> P x \<Longrightarrow> P' y \<Longrightarrow> x=y"
  shows "\<lbrakk> cmap_relation a c f r; cmap_relation a' c f r; \<forall>x \<in> ran a. P x; \<forall>x \<in> ran a'. P' x \<rbrakk> \<Longrightarrow> a' = a"
  using assms
  apply (clarsimp simp: ran_def)
  apply (rule cmap_relation_unique_0[OF inj_f, where P="\<lambda>_. P" and P'="\<lambda>_. P'"])
      defer
      apply assumption+
    apply fastforce
   apply fastforce
  apply fastforce
  done

lemma cmap_relation_unique:
  assumes inj_f: "inj f"
  assumes r: "\<And>x y z. r x z \<Longrightarrow> r y z \<Longrightarrow> x=y"
  shows "cmap_relation a c f r \<Longrightarrow> cmap_relation a' c f r \<Longrightarrow> a' = a"
  apply (rule cmap_relation_unique'[OF inj_f])
      defer
      apply (fastforce intro: r)+
  done

lemma cpspace_cte_relation_unique:
  assumes "cpspace_cte_relation ah ch" "cpspace_cte_relation ah' ch"
  shows   "map_to_ctes ah' = map_to_ctes ah"
  apply (rule cmap_relation_unique[OF inj_Ptr _ assms])
  by (clarsimp simp: ccte_relation_def Some_the[symmetric]) (drule sym, simp)

lemma inj_tcb_ptr_to_ctcb_ptr: "inj tcb_ptr_to_ctcb_ptr"
  by (rule kernel.inj_tcb_ptr_to_ctcb_ptr)

lemma cregs_relation_imp_eq:
  "cregs_relation f x \<Longrightarrow> cregs_relation g x \<Longrightarrow> f=g"
  by (auto simp: cregs_relation_def)

lemma ccontext_relation_imp_eq:
  "ccontext_relation f x \<Longrightarrow> ccontext_relation g x \<Longrightarrow> f=g"
  unfolding ccontext_relation_def
  apply (cases f, cases g)
  apply (auto dest: cregs_relation_imp_eq)
  done

lemma map_to_ctes_tcb_ctes:
  notes if_cong[cong]
  shows
  "ctes_of s' = ctes_of s \<Longrightarrow>
   ko_at' tcb p s \<Longrightarrow> ko_at' tcb' p s' \<Longrightarrow>
   \<forall>x\<in>ran tcb_cte_cases. fst x tcb' = fst x tcb"
  apply (clarsimp simp add: ran_tcb_cte_cases)
  apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_opt_tcb
                 split: kernel_object.splits)
  apply (case_tac ko, simp_all, clarsimp)
  apply (clarsimp simp: objBits_type[of "KOTCB tcb" "KOTCB undefined"]
                        objBits_type[of "KOTCB tcb'" "KOTCB undefined"])
  apply (rule conjI)
   apply (drule ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')+
   apply (clarsimp simp: map_to_ctes_def Let_def fun_eq_iff)
   apply (drule_tac x=p in spec, simp)
  apply (rule conjI)
   apply (clarsimp simp: map_to_ctes_def Let_def fun_eq_iff)
   apply (drule_tac x="p+0x20" in spec, simp add: objBitsKO_def)
   apply (frule_tac s1=s in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (frule_tac s1=s' in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (drule (1) ps_clear_32)+
   apply (simp add: is_aligned_add_helper[of _ 10 "0x20", simplified]
                    split_def objBits_simps')
  apply (rule conjI)
   apply (clarsimp simp: map_to_ctes_def Let_def fun_eq_iff)
   apply (drule_tac x="p+0x40" in spec, simp add: objBitsKO_def)
   apply (frule_tac s1=s in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (frule_tac s1=s' in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (drule (1) ps_clear_is_aligned_ctes_None(1))+
   apply (simp add: is_aligned_add_helper[of _ 10 "0x40", simplified]
                    split_def objBits_simps')
  apply (rule conjI)
   apply (clarsimp simp: map_to_ctes_def Let_def fun_eq_iff)
   apply (drule_tac x="p+0x60" in spec, simp add: objBitsKO_def)
   apply (frule_tac s1=s in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (frule_tac s1=s' in ps_clear_def3[THEN iffD1,rotated 2],
          assumption, simp add: objBits_simps')
   apply (drule (1) ps_clear_is_aligned_ctes_None(2))+
   apply (simp add: is_aligned_add_helper[of _ 10 "0x60", simplified]
                    split_def objBits_simps')
  apply (clarsimp simp: map_to_ctes_def Let_def fun_eq_iff)
  apply (drule_tac x="p+0x80" in spec, simp add: objBitsKO_def)
  apply (frule_tac s1=s in ps_clear_def3[THEN iffD1,rotated 2],
         assumption, simp add: objBits_simps')
  apply (frule_tac s1=s' in ps_clear_def3[THEN iffD1,rotated 2],
         assumption, simp add: objBits_simps')
  apply (drule (1) ps_clear_is_aligned_ctes_None(3))+
  apply (simp add: is_aligned_add_helper[of _ 10 "0x80", simplified]
                   split_def objBits_simps')
  done

lemma cfault_rel_imp_eq:
  "cfault_rel x a b \<Longrightarrow> cfault_rel y a b \<Longrightarrow> x=y"
  by (clarsimp simp: cfault_rel_def is_cap_fault_def
              split: if_split_asm seL4_Fault_CL.splits)

lemma cthread_state_rel_imp_eq:
  "cthread_state_relation x z \<Longrightarrow> cthread_state_relation y z \<Longrightarrow> x=y"
  apply (simp add: cthread_state_relation_def split_def)
  apply (cases x)
  apply (cases y, simp_all add: ThreadState_BlockedOnReceive_def
    ThreadState_BlockedOnReply_def ThreadState_BlockedOnNotification_def
    ThreadState_Running_def ThreadState_Inactive_def
    ThreadState_IdleThreadState_def ThreadState_BlockedOnSend_def
    ThreadState_Restart_def)+
  done

lemma ksPSpace_valid_objs_tcbBoundNotification_nonzero:
  "\<exists>s. ksPSpace s = ah \<and> no_0_obj' s \<and> valid_objs' s
     \<Longrightarrow> map_to_tcbs ah p = Some tcb \<Longrightarrow> tcbBoundNotification tcb \<noteq> Some 0"
  apply (clarsimp simp: map_comp_def split: option.splits)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp: projectKOs valid_obj'_def valid_tcb'_def)
  done

lemma atcbContextGet_inj[simp]:
  "(atcbContextGet t = atcbContextGet t') = (t = t')"
  by (cases t, cases t') (simp add: atcbContextGet_def)

lemma ccontext_relation_imp_eq2:
  "\<lbrakk>ccontext_relation (atcbContextGet t) x; ccontext_relation (atcbContextGet t') x\<rbrakk> \<Longrightarrow> t = t'"
  by (auto dest: ccontext_relation_imp_eq)

lemma cpspace_tcb_relation_unique:
  assumes tcbs: "cpspace_tcb_relation ah ch" "cpspace_tcb_relation ah' ch"
      and   vs: "\<exists>s. ksPSpace s = ah \<and> no_0_obj' s \<and> valid_objs' s"
      and   vs': "\<exists>s. ksPSpace s = ah' \<and> no_0_obj' s \<and> valid_objs' s"
  assumes ctes: " \<forall>tcb tcb'. (\<exists>p. map_to_tcbs ah p = Some tcb \<and>
                                  map_to_tcbs ah' p = Some tcb') \<longrightarrow>
                  (\<forall>x\<in>ran tcb_cte_cases. fst x tcb' = fst x tcb)"
  shows "map_to_tcbs ah' = map_to_tcbs ah"
  using tcbs(2) tcbs(1)
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_tcb_ptr_to_ctcb_ptr])+
  apply (simp add: tcb_ptr_to_ctcb_ptr_def[abs_def] ctcb_offset_def)
  apply (rule ext)
  apply (case_tac "x:dom (map_to_tcbs ah)")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   apply clarsimp
   apply (rename_tac p x y)
   apply (cut_tac ctes)
   apply (drule_tac x=x in spec, drule_tac x=y in spec, erule impE, fastforce)
   apply (frule ksPSpace_valid_objs_tcbBoundNotification_nonzero[OF vs])
   apply (frule ksPSpace_valid_objs_tcbBoundNotification_nonzero[OF vs'])
   apply (thin_tac "map_to_tcbs x y = Some z" for x y z)+
   apply (case_tac x, case_tac y, case_tac "the (clift ch (tcb_Ptr (p+0x200)))")
   apply (clarsimp simp: ctcb_relation_def ran_tcb_cte_cases)
   apply (clarsimp simp: option_to_ptr_def option_to_0_def split: option.splits)
   apply (auto simp: cfault_rel_imp_eq cthread_state_rel_imp_eq carch_tcb_relation_def
                     ccontext_relation_imp_eq2 up_ucast_inj_eq ctcb_size_bits_def)
  done

lemma tcb_queue_rel_clift_unique:
  "tcb_queue_relation gn gp' (clift s) as pp cp \<Longrightarrow>
   tcb_queue_relation gn gp' (clift s) as' pp cp \<Longrightarrow> as' = as"
by (rule tcb_queue_rel_unique, rule lift_t_NULL)

lemma tcb_queue_rel'_clift_unique:
  "tcb_queue_relation' gn gp' (clift s) as pp cp \<Longrightarrow>
   tcb_queue_relation' gn gp' (clift s) as' pp cp \<Longrightarrow> as' = as"
  by (clarsimp simp add: tcb_queue_relation'_def)
     (rule tcb_queue_rel_clift_unique)

lemma cpspace_ep_relation_unique:
  assumes "cpspace_ep_relation ah ch" "cpspace_ep_relation ah' ch"
  shows   "map_to_eps ah' = map_to_eps ah"
  apply (rule cmap_relation_unique[OF inj_Ptr _ assms])
  apply (clarsimp simp: EPState_Idle_def EPState_Recv_def EPState_Send_def
             cendpoint_relation_def Let_def tcb_queue_rel'_clift_unique
           split: endpoint.splits)
  done

lemma ksPSpace_valid_pspace_ntfnBoundTCB_nonzero:
  "\<exists>s. ksPSpace s = ah \<and> valid_pspace' s
     \<Longrightarrow> map_to_ntfns ah p = Some ntfn \<Longrightarrow> ntfnBoundTCB ntfn \<noteq> Some 0"
  apply (clarsimp simp: map_comp_def valid_pspace'_def split: option.splits)
  apply (erule(1) valid_objsE')
  apply (clarsimp simp: projectKOs valid_obj'_def valid_ntfn'_def)
  done

lemma tcb_ptr_to_ctcb_ptr_inj:
  "tcb_ptr_to_ctcb_ptr x = tcb_ptr_to_ctcb_ptr y \<Longrightarrow> x = y"
  by (auto simp: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)

lemma cpspace_ntfn_relation_unique:
  assumes ntfns: "cpspace_ntfn_relation ah ch" "cpspace_ntfn_relation ah' ch"
      and   vs: "\<exists>s. ksPSpace s = ah \<and> valid_pspace' s"
      and   vs': "\<exists>s. ksPSpace s = ah' \<and> valid_pspace' s"
  shows   "map_to_ntfns ah' = map_to_ntfns ah"
  using ntfns
  apply (clarsimp simp: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_Ptr])+
  apply simp
  apply (rule ext)
  apply (case_tac "x:dom (map_to_ntfns ah)")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   apply (clarsimp)
   apply (frule ksPSpace_valid_pspace_ntfnBoundTCB_nonzero[OF vs])
   apply (frule ksPSpace_valid_pspace_ntfnBoundTCB_nonzero[OF vs'])
   apply (cut_tac vs vs')
   apply (clarsimp simp: valid_pspace'_def)
   apply (frule (2) map_to_ko_atI)
   apply (frule_tac v=ya in map_to_ko_atI, simp+)
   apply (clarsimp dest!: obj_at_valid_objs' simp: projectKOs split: option.splits)
   apply (thin_tac "map_to_ntfns x y = Some z" for x y z)+
   apply (case_tac y, case_tac ya, case_tac "the (clift ch (ntfn_Ptr x))")
   by (auto simp: NtfnState_Active_def NtfnState_Idle_def NtfnState_Waiting_def typ_heap_simps
                     cnotification_relation_def Let_def tcb_queue_rel'_clift_unique
                     option_to_ctcb_ptr_def valid_obj'_def valid_ntfn'_def valid_bound_tcb'_def
                     kernel.tcb_at_not_NULL tcb_ptr_to_ctcb_ptr_inj
              split: ntfn.splits option.splits) (* long *)

declare of_bool_eq_iff[simp]

lemma cpspace_pte_relation_unique:
  assumes "cpspace_pte_relation ah ch" "cpspace_pte_relation ah' ch"
  shows   "map_to_ptes ah' = map_to_ptes ah"
  apply (rule cmap_relation_unique'[OF inj_Ptr _ assms, where P=\<top> and P'=\<top>]; simp)
  apply (simp add: cpte_relation_def Let_def ucast_id
                   writable_from_vm_rights_def readable_from_vm_rights_def
              split: pte.splits vmrights.splits)
  done

lemma is_aligned_no_overflow_0:
  "\<lbrakk> is_aligned x n; y \<le> 2^n-1; y \<noteq> 0 \<rbrakk> \<Longrightarrow> 0 < x + y"
  apply (drule is_aligned_no_overflow)
  apply simp
  by unat_arith

abbreviation
  "is_aligned_opt x n \<equiv> case x of None \<Rightarrow> True | Some y \<Rightarrow> is_aligned y n"

lemma option_to_ctcb_ptr_inj:
  "\<lbrakk> is_aligned_opt a tcbBlockSizeBits; is_aligned_opt b tcbBlockSizeBits \<rbrakk>
    \<Longrightarrow> (option_to_ctcb_ptr a = option_to_ctcb_ptr b) = (a = b)"
  apply (simp add: option_to_ctcb_ptr_def tcb_ptr_to_ctcb_ptr_def ctcb_offset_defs objBits_defs
            split: option.splits)
   apply (erule is_aligned_no_overflow_0; simp)
  apply (erule is_aligned_no_overflow_0; simp)
  done

(* FIXME RISCV
lemma cpspace_asidpool_relation_unique:
  assumes invs: "\<forall>x\<in>ran (map_to_asidpools ah). wf_asid_pool' x"
                "\<forall>x\<in>ran (map_to_asidpools ah'). wf_asid_pool' x"
  assumes rels: "cpspace_asidpool_relation ah ch"
                "cpspace_asidpool_relation ah' ch"
  shows   "map_to_asidpools ah' = map_to_asidpools ah"
  (* FIXME: Should we generalize cmap_relation_unique, instead? *)
  using rels
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_Ptr])+
  apply simp
  apply (rule ext)
  apply (case_tac "x:dom (map_to_asidpools ah)")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   using invs
   apply (clarsimp simp: casid_pool_relation_def Let_def
                  split: asidpool.splits asid_pool_C.splits)
   apply (rename_tac "fun" array)
   apply (drule bspec, fastforce)+
   apply (drule array_relation_to_map)+
   apply (rule ext, rename_tac y)
   apply (drule_tac x=y in spec)+
   apply clarsimp
   sorry (* FIXME RISCV
   apply (case_tac "y\<le>2^asid_low_bits - 1", simp)
    apply (simp add: asid_map_relation_def split: option.splits asid_map_CL.splits)
   apply (simp add: atLeastAtMost_def atLeast_def atMost_def dom_def
                    Collect_mono2)
   apply (drule_tac x=y in spec)+
   apply auto
  done
  *)

lemma valid_objs'_imp_wf_asid_pool':
  "valid_objs' s \<Longrightarrow> \<forall>x\<in>ran (map_to_asidpools (ksPSpace s)). wf_asid_pool' x"
  apply (clarsimp simp: valid_objs'_def ran_def)
  apply (case_tac "ksPSpace s a", simp+)
  apply (rename_tac y, drule_tac x=y in spec)
  apply (case_tac y, simp_all add: projectKO_opt_asidpool)
  apply (clarsimp simp: valid_obj'_def
                 split: arch_kernel_object.splits)
  done
*)

lemma cpspace_user_data_relation_unique:
  "\<lbrakk>cmap_relation (heap_to_user_data ah bh) (clift ch) Ptr cuser_user_data_relation;
    cmap_relation (heap_to_user_data ah' bh')(clift ch) Ptr cuser_user_data_relation\<rbrakk>
   \<Longrightarrow> map_to_user_data ah' = map_to_user_data ah"
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_Ptr])+
  apply simp
  apply (rule ext)
  apply (case_tac "x:dom (heap_to_user_data ah bh)")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   apply (clarsimp simp add: cuser_user_data_relation_def heap_to_user_data_def)
   apply (rule ccontr)
   apply (case_tac z, case_tac za)
   apply simp
  apply (fastforce simp: dom_def heap_to_user_data_def Collect_eq)
  done

lemma cpspace_device_data_relation_unique:
  "\<lbrakk>cmap_relation (heap_to_device_data ah bh) (clift ch) Ptr cuser_device_data_relation;
    cmap_relation (heap_to_device_data ah' bh')(clift ch) Ptr cuser_device_data_relation\<rbrakk>
   \<Longrightarrow> map_to_user_data_device ah' = map_to_user_data_device ah"
  apply (clarsimp simp add: cmap_relation_def)
  apply (drule inj_image_inv[OF inj_Ptr])+
  apply simp
  apply (rule ext)
  apply (case_tac "x:dom (heap_to_device_data ah bh)")
   apply (drule bspec, assumption)+
   apply (simp add: dom_def Collect_eq, drule_tac x=x in spec)
   apply (clarsimp simp add: heap_to_device_data_def)
   apply (rule ccontr)
   apply (case_tac z, case_tac za)
   apply simp
  apply (fastforce simp: dom_def heap_to_device_data_def Collect_eq)
  done

lemmas projectKO_opts = projectKO_opt_ep projectKO_opt_ntfn projectKO_opt_tcb
                        projectKO_opt_pte
                        projectKO_opt_asidpool projectKO_opt_cte
                        projectKO_opt_user_data projectKO_opt_user_data_device

(* Following from the definition of map_to_ctes,
   there are two kinds of capability tables, namely CNodes and TCBs.
   I would like to talk specifically about CNode Entries.
   Hence, the name cnes. *)
abbreviation
  map_to_cnes :: "(word32 \<rightharpoonup> kernel_object) \<Rightarrow> word32 \<rightharpoonup> cte"
where
  "map_to_cnes \<equiv> (\<circ>\<^sub>m) projectKO_opt"

(* FIXME RISCV move: used to be in ADT_H *)
lemma ctes_of_cte_wp_atxD:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' ((=) cte) p s"
  by (simp add: KHeap_R.cte_wp_at_ctes_of)

lemma map_to_cnes_eq:
  assumes aligned: "pspace_aligned' s"   and aligned': "pspace_aligned' s'"
  assumes distinct: "pspace_distinct' s" and distinct': "pspace_distinct' s'"
  shows
  "ctes_of s' = ctes_of s \<Longrightarrow>
   map_to_tcbs (ksPSpace s') = map_to_tcbs (ksPSpace s) \<Longrightarrow>
   (projectKO_opt::kernel_object\<rightharpoonup>cte) \<circ>\<^sub>m ksPSpace s' =
   (projectKO_opt::kernel_object\<rightharpoonup>cte) \<circ>\<^sub>m ksPSpace s"
  apply (rule ext)
  apply (simp add: fun_eq_iff)
  apply (drule_tac x=x in spec)
  apply (case_tac "ksPSpace s x", case_tac "ksPSpace s' x", simp)
   apply (clarsimp simp add: projectKO_opt_cte split: kernel_object.splits)
   apply (frule SR_lemmas_C.ctes_of_ksI[OF _ aligned' distinct'], simp)
   apply (drule_tac t="ctes_of s x" in sym)
   apply (frule ctes_of_cte_at, simp add: cte_at'_obj_at')
   apply (elim disjE)
    apply (simp add: obj_at'_def)
   apply (clarsimp simp add: obj_at'_real_def ko_wp_at'_def)
   apply (drule_tac x="x-n" in spec)
   apply (clarsimp simp add: map_comp_def projectKO_opt_tcb
                   split: option.splits kernel_object.splits)
   apply (frule_tac x="x-n" in pspace_distinctD'[OF _ distinct'])
   apply (simp add: objBitsKO_def)
   apply (erule_tac y=x and s=s' and getF=a and setF=b
          in tcb_space_clear[rotated], assumption+, simp+)
  apply (case_tac "ksPSpace s' x")
   apply (clarsimp simp add: projectKO_opt_cte split: kernel_object.splits)
   apply (frule SR_lemmas_C.ctes_of_ksI[OF _ aligned distinct], simp)
   apply (frule ctes_of_cte_at, simp add: cte_at'_obj_at')
   apply (elim disjE)
    apply (simp add: obj_at'_def)
   apply (clarsimp simp add: obj_at'_real_def ko_wp_at'_def)
   apply (drule_tac x="x-n" in spec)
   apply (clarsimp simp add: map_comp_def projectKO_opt_tcb
                   split: option.splits kernel_object.splits)
   apply (frule_tac x="x-n" in pspace_distinctD'[OF _ distinct])
   apply (simp add: objBitsKO_def)
   apply (erule_tac y=x and s=s and getF=a and setF=b
          in tcb_space_clear[rotated], assumption+, simp+)
  apply (case_tac "EX cte. ksPSpace s x = Some (KOCTE cte)", clarsimp)
   apply (frule SR_lemmas_C.ctes_of_ksI[OF _ aligned distinct], simp)
   apply (drule ctes_of_cte_wpD)+
   apply (simp add: cte_wp_at'_obj_at')
   apply (elim disjE)
      apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def)
     apply (thin_tac "Bex A P" for A P)
     apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_opt_cte)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def
                          projectKO_opt_cte projectKO_opt_tcb)
    apply (case_tac ko, simp_all, clarsimp simp: objBitsKO_def)
    apply (erule_tac y=x and s=s' and getF=a and setF=b
           in tcb_space_clear[rotated], assumption+)
     apply (drule_tac x=x in spec, simp add: projectKO_opt_tcb)
    apply simp
   apply (thin_tac "Bex A P" for A P)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def
                         projectKO_opt_cte projectKO_opt_tcb)
   apply (case_tac ko, simp_all, clarsimp simp: objBitsKO_def)
   apply (erule_tac y=x and s=s and getF=a and setF=b
          in tcb_space_clear[rotated], assumption+, simp+)
  apply (case_tac "EX cte. ksPSpace s' x = Some (KOCTE cte)", clarsimp)
   apply (frule SR_lemmas_C.ctes_of_ksI[OF _ aligned' distinct'], simp)
   apply (drule_tac t="ctes_of s x" in sym)
   apply (drule ctes_of_cte_wpD)+
   apply (simp add: cte_wp_at'_obj_at')
   apply (elim disjE)
    apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def projectKO_opt_cte)
   apply (clarsimp simp: obj_at'_real_def ko_wp_at'_def
                         projectKO_opt_cte projectKO_opt_tcb)
   apply (case_tac ko, simp_all, clarsimp simp: objBitsKO_def)
   apply (erule_tac y=x and s=s and getF=aa and setF=b
          in tcb_space_clear[rotated], assumption+)
    apply (drule_tac x=x in spec, simp add: projectKO_opt_tcb)
   apply simp
  apply (clarsimp simp: projectKO_opt_cte split: kernel_object.splits)
  done

(* FIXME RISCV
lemma valid_objs'_valid_pte'_ran:
  "valid_objs' s \<Longrightarrow> \<forall>x\<in>ran (map_to_ptes (ksPSpace s)). valid_pte' x s"
  apply (clarsimp simp: valid_objs'_def ran_def)
  apply (case_tac "ksPSpace s a", simp+)
  apply (rename_tac y, drule_tac x=y in spec)
  apply (case_tac y, simp_all add: projectKOs)
  apply (clarsimp simp: valid_obj'_def
                 split: arch_kernel_object.splits)
  done
*)

lemma cpspace_relation_unique:
  assumes valid_pspaces: "valid_pspace' s" "valid_pspace' s'"
  shows "cpspace_relation (ksPSpace s) bh ch \<Longrightarrow>
         cpspace_relation (ksPSpace s') bh ch \<Longrightarrow>
         (ksPSpace s') = (ksPSpace (s::kernel_state))" (is "PROP ?goal")
proof -
  from valid_pspaces
  have no_kdatas: "KOKernelData \<notin> ran (ksPSpace s)"
                  "KOKernelData \<notin> ran (ksPSpace s')"
    by (auto simp add: valid_pspace'_def valid_objs'_def valid_obj'_def)

  from valid_pspaces
  have valid_objs: "valid_objs' s"    and valid_objs': "valid_objs' s'"
   and aligned: "pspace_aligned' s"   and aligned': "pspace_aligned' s'"
   and distinct: "pspace_distinct' s" and distinct': "pspace_distinct' s'"
   and no_0_objs: "no_0_obj' s"       and no_0_objs': "no_0_obj' s'"
    by auto

  show "PROP ?goal"
    apply (clarsimp simp add: cpspace_relation_def)
    apply (drule (1) cpspace_cte_relation_unique)
    apply (drule (1) cpspace_ep_relation_unique)
    apply (drule (1) cpspace_ntfn_relation_unique)
      apply (fastforce intro: valid_pspaces)
     apply (fastforce intro: valid_pspaces)
    apply (drule (1) cpspace_pte_relation_unique)
  sorry (* FIXME RISCV: casid_pool_relation does not guarantee an inverse due to valid_obj'
                        placing no constraints on asid pool domain
    apply (drule (1) cpspace_asidpool_relation_unique[
                       OF valid_objs'_imp_wf_asid_pool'[OF valid_objs]
                          valid_objs'_imp_wf_asid_pool'[OF valid_objs']])
    apply (drule (1) cpspace_tcb_relation_unique)
       apply (fastforce intro: no_0_objs no_0_objs' valid_objs valid_objs')
      apply (fastforce intro: no_0_objs no_0_objs' valid_objs valid_objs')
     apply (intro allI impI,elim exE conjE)
     apply (rule_tac p=p in map_to_ctes_tcb_ctes, assumption)
      apply (frule (1) map_to_ko_atI[OF _ aligned distinct])
     apply (frule (1) map_to_ko_atI[OF _ aligned' distinct'])
    apply (drule (1) map_to_cnes_eq[OF aligned aligned' distinct distinct'])
    apply (drule (1) cpspace_user_data_relation_unique)
    apply (drule (1)  cpspace_device_data_relation_unique)
    apply (thin_tac "cmap_relation a c f r" for a c f r)+
    apply (cut_tac no_kdatas)
    apply (clarsimp simp add: ran_def fun_eq_iff)
    apply (drule_tac x=x in spec)+
    apply (case_tac "ksPSpace s x")
     apply (case_tac "ksPSpace s' x", simp)
     apply (case_tac a, simp_all add: projectKO_opts
                               split: arch_kernel_object.splits)
    by (clarsimp simp: projectKO_opts map_comp_def
                split: kernel_object.splits arch_kernel_object.splits
                       option.splits)
    *)
qed
(*<<< end showing that cpspace_relation is actually unique *)

lemma ksPSpace_eq_imp_ko_wp_at'_eq:
  "ksPSpace s' = ksPSpace s \<Longrightarrow> ko_wp_at' P a s' = ko_wp_at' P a s"
  by (clarsimp simp: ko_wp_at'_def ps_clear_def)

lemma ksPSpace_eq_imp_obj_at'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "obj_at' P a s' = obj_at' P a s"
  by (clarsimp simp: obj_at'_real_def ksPSpace_eq_imp_ko_wp_at'_eq[OF ksPSpace])

lemma ksPSpace_eq_imp_typ_at'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "typ_at' P a s' = typ_at' P a s"
  by (simp add: typ_at'_def ksPSpace_eq_imp_ko_wp_at'_eq[OF ksPSpace])

lemma ksPSpace_eq_imp_valid_cap'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "valid_cap' c s' = valid_cap' c s"
  by (auto simp: valid_cap'_def page_table_at'_def frame_at'_def
                 valid_untyped'_def
                 ksPSpace_eq_imp_obj_at'_eq[OF ksPSpace]
                 ksPSpace_eq_imp_typ_at'_eq[OF ksPSpace]
                 ksPSpace_eq_imp_ko_wp_at'_eq[OF ksPSpace]
                 valid_arch_cap'_def wellformed_acap'_def
          split: capability.splits zombie_type.splits arch_capability.splits)

lemma ksPSpace_eq_imp_valid_tcb'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "valid_tcb' tcb s' = valid_tcb' tcb s"
  by (auto simp: ksPSpace_eq_imp_obj_at'_eq[OF ksPSpace]
                 ksPSpace_eq_imp_valid_cap'_eq[OF ksPSpace]
                 ksPSpace_eq_imp_typ_at'_eq[OF ksPSpace]
                 valid_tcb'_def valid_tcb_state'_def valid_bound_ntfn'_def
          split: thread_state.splits option.splits)

(* FIXME RISCV
lemma ksPSpace_eq_imp_valid_arch_obj'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "valid_arch_obj' ao s' = valid_arch_obj' ao s"
  apply (case_tac ao, simp)
     apply (rename_tac obj, case_tac obj; simp add: valid_mapping'_def)+
  done
*)

lemma ksPSpace_eq_imp_valid_objs'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "valid_objs' s' = valid_objs' s"
  using assms
  by (clarsimp simp: valid_objs'_def valid_obj'_def valid_ep'_def
                     ksPSpace_eq_imp_obj_at'_eq[OF ksPSpace]
                     ksPSpace_eq_imp_valid_tcb'_eq[OF ksPSpace]
                     ksPSpace_eq_imp_valid_cap'_eq[OF ksPSpace]
(* FIXME RISCV                     ksPSpace_eq_imp_valid_arch_obj'_eq[OF ksPSpace] *)
                     valid_ntfn'_def valid_cte'_def valid_bound_tcb'_def
              split: kernel_object.splits endpoint.splits ntfn.splits option.splits)

lemma ksPSpace_eq_imp_valid_pspace'_eq:
  assumes ksPSpace: "ksPSpace s' = ksPSpace s"
  shows "valid_pspace' s = valid_pspace' s'"
  using assms
  by (clarsimp simp: valid_pspace'_def pspace_aligned'_def
        pspace_distinct'_def ps_clear_def no_0_obj'_def valid_mdb'_def
        pspace_canonical'_def pspace_in_kernel_mappings'_def
        ksPSpace_eq_imp_valid_objs'_eq[OF ksPSpace])

(* The awkwardness of this definition is only caused by the fact
   that valid_pspace' is defined over the complete state. *)
definition
  cstate_to_pspace_H :: "globals \<Rightarrow> machine_word \<rightharpoonup> kernel_object"
where
  "cstate_to_pspace_H c \<equiv>
   THE h. valid_pspace' (undefined\<lparr>ksPSpace := h\<rparr>) \<and>
          cpspace_relation h (underlying_memory (cstate_to_machine_H c))
                             (t_hrs_' c)"

lemma cstate_to_pspace_H_correct:
  "valid_pspace' a \<Longrightarrow>
   cpspace_relation (ksPSpace a)
     (underlying_memory (cstate_to_machine_H c)) (t_hrs_' c) \<Longrightarrow>
   cstate_to_pspace_H c = ksPSpace a"
  apply (simp add: cstate_to_pspace_H_def)
  apply (rule the_equality, simp)
   apply (rule_tac s1=a in ksPSpace_eq_imp_valid_pspace'_eq[THEN iffD1],
          clarsimp+)
  apply (drule (2) cpspace_relation_unique, simp+)
  done

end

context state_rel begin

lemma cDomScheduleIdx_to_H_correct:
  assumes valid: "valid_state' as"
  assumes cstate_rel: "cstate_relation as cs"
  assumes ms: "cstate_to_machine_H cs = observable_memory (ksMachineState as) (user_mem' as)"
  shows "unat (ksDomScheduleIdx_' cs) = ksDomScheduleIdx as"
  using assms
  by (clarsimp simp: cstate_relation_def Let_def observable_memory_def valid_state'_def
                     newKernelState_def unat_of_nat_eq cdom_schedule_relation_def)

definition
  cDomSchedule_to_H :: "(dschedule_C['b :: finite]) \<Rightarrow> (8 word \<times> machine_word) list"
where
  "cDomSchedule_to_H cs \<equiv> THE as. cdom_schedule_relation as cs"

(* FIXME: The assumption of this is unnecessarily strong *)
lemma cDomSchedule_to_H_correct:
  assumes valid: "valid_state' as"
  assumes cstate_rel: "cstate_relation as cs"
  assumes ms: "cstate_to_machine_H cs = observable_memory (ksMachineState as) (user_mem' as)"
  shows "cDomSchedule_to_H kernel_all_global_addresses.ksDomSchedule = kernel_state.ksDomSchedule as"
  using assms
  apply (clarsimp simp: cstate_relation_def Let_def valid_state'_def newKernelState_def cDomSchedule_to_H_def cdom_schedule_relation_def)
  apply (rule the_equality, simp)
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp: dom_schedule_entry_relation_def)
  apply (drule_tac x=i in spec)+
  apply (rule prod_eqI)
   apply (subst up_ucast_inj_eq[where 'b=64, symmetric])
    apply auto
  done

definition
  cbitmap_L1_to_H :: "machine_word[16] \<Rightarrow> (8 word \<Rightarrow> machine_word)"
where
  "cbitmap_L1_to_H l1 \<equiv> \<lambda>d. if d \<le> maxDomain then l1.[unat d] else 0"

definition
  cbitmap_L2_to_H :: "machine_word[4][16] \<Rightarrow> (8 word \<times> nat \<Rightarrow> machine_word)"
where
  "cbitmap_L2_to_H l2 \<equiv> \<lambda>(d, i).
    if d \<le> maxDomain \<and> i < l2BitmapSize
    then l2.[unat d].[i] else 0"

lemma cbitmap_L1_to_H_correct:
  "cbitmap_L1_relation cs as \<Longrightarrow>
   cbitmap_L1_to_H cs = as"
   unfolding cbitmap_L1_to_H_def cbitmap_L1_relation_def
   apply (rule ext)
   apply (clarsimp split: if_split)
   done

lemma cbitmap_L2_to_H_correct:
  "cbitmap_L2_relation cs as \<Longrightarrow>
   cbitmap_L2_to_H cs = as"
   unfolding cbitmap_L2_to_H_def cbitmap_L2_relation_def
   apply (rule ext)
   apply (clarsimp split: if_split)
   done

definition
  mk_gsUntypedZeroRanges
where
  "mk_gsUntypedZeroRanges s
      = ran (untypedZeroRange \<circ>\<^sub>m (option_map cteCap o map_to_ctes (cstate_to_pspace_H s)))"

lemma cpspace_user_data_relation_user_mem'[simp]:
  "\<lbrakk>pspace_aligned' as;pspace_distinct' as\<rbrakk> \<Longrightarrow> cpspace_user_data_relation (ksPSpace as) (option_to_0 \<circ> user_mem' as) (t_hrs_' cs)
  = cpspace_user_data_relation (ksPSpace as)  (underlying_memory (ksMachineState as)) (t_hrs_' cs)"
  by (simp add: cmap_relation_def)

lemma cpspace_device_data_relation_user_mem'[simp]:
  "cpspace_device_data_relation (ksPSpace as) (option_to_0 \<circ> user_mem' as) (t_hrs_' cs)
  = cpspace_device_data_relation (ksPSpace as)  (underlying_memory (ksMachineState as)) (t_hrs_' cs)"
  apply (clarsimp simp: cmap_relation_def cuser_user_data_device_relation_def heap_to_device_data_def)
  apply (rule_tac arg_cong[where  f = "%x. x = y" for y])
  by auto

lemma mk_gsUntypedZeroRanges_correct:
  assumes valid: "valid_state' as"
  assumes cstate_rel: "cstate_relation as cs"
  shows "mk_gsUntypedZeroRanges cs = gsUntypedZeroRanges as"
  using assms
  apply (clarsimp simp: valid_state'_def untyped_ranges_zero_inv_def
                        mk_gsUntypedZeroRanges_def cteCaps_of_def)
  apply (subst cstate_to_pspace_H_correct[where c=cs], simp_all)
  apply (clarsimp simp: cstate_relation_def Let_def)
  apply (subst cstate_to_machine_H_correct, assumption, simp_all)
   apply (clarsimp simp: cpspace_relation_def)+
  apply (clarsimp simp: observable_memory_def valid_pspace'_def)
  done


definition
  cstate_to_H :: "globals \<Rightarrow> kernel_state"
where
  "cstate_to_H s \<equiv>
   \<lparr>ksPSpace = cstate_to_pspace_H s,
    gsUserPages = fst (ghost'state_' s), gsCNodes = fst (snd (ghost'state_' s)),
    gsUntypedZeroRanges = mk_gsUntypedZeroRanges s,
    gsMaxObjectSize = (let v = unat (gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' s))
        in if v = 0 then card (UNIV :: machine_word set) else v),
    ksDomScheduleIdx = unat (ksDomScheduleIdx_' s),
    ksDomSchedule = cDomSchedule_to_H kernel_all_global_addresses.ksDomSchedule,
    ksCurDomain = ucast (ksCurDomain_' s),
    ksDomainTime = ksDomainTime_' s,
    ksReadyQueues = cready_queues_to_H (clift (t_hrs_' s)) (ksReadyQueues_' s),
    ksReadyQueuesL1Bitmap = cbitmap_L1_to_H (ksReadyQueuesL1Bitmap_' s),
    ksReadyQueuesL2Bitmap = cbitmap_L2_to_H (ksReadyQueuesL2Bitmap_' s),
    ksCurThread = ctcb_ptr_to_tcb_ptr (ksCurThread_' s),
    ksIdleThread = ctcb_ptr_to_tcb_ptr (ksIdleThread_' s),
    ksSchedulerAction = cscheduler_action_to_H (ksSchedulerAction_' s),
    ksInterruptState =
      cint_state_to_H intStateIRQNode_array_Ptr (intStateIRQTable_' s),
    ksWorkUnitsCompleted = ksWorkUnitsCompleted_' s,
    ksArchState = carch_state_to_H s,
    ksMachineState = cstate_to_machine_H s\<rparr>"

end

context kernel_m begin

lemma trivial_eq_conj: "B = C \<Longrightarrow> (A \<and> B) = (A \<and> C)"
  by simp

lemma cstate_to_H_correct:
  assumes valid: "valid_state' as"
  assumes cstate_rel: "cstate_relation as cs"
  shows "cstate_to_H cs = as \<lparr>ksMachineState:=  observable_memory (ksMachineState as) (user_mem' as)\<rparr>"
  apply (subgoal_tac "cstate_to_machine_H cs = observable_memory (ksMachineState as) (user_mem' as)")
   apply (rule kernel_state.equality, simp_all add: cstate_to_H_def)
                      apply (rule cstate_to_pspace_H_correct)
                     using valid
                     apply (simp add: valid_state'_def)
                    using cstate_rel valid
                    apply (clarsimp simp: cstate_relation_def cpspace_relation_def Let_def
                      observable_memory_def valid_state'_def
                      valid_pspace'_def)
                   using cstate_rel
                   apply (clarsimp simp: cstate_relation_def cpspace_relation_def Let_def prod_eq_iff)
                  using cstate_rel
                  apply (clarsimp simp: cstate_relation_def cpspace_relation_def  Let_def prod_eq_iff)
                 using valid cstate_rel
                 apply (rule mk_gsUntypedZeroRanges_correct)
                subgoal
                using cstate_rel
                by (fastforce simp: cstate_relation_def cpspace_relation_def
                                    Let_def ghost_size_rel_def unat_eq_0
                            split: if_split)
               using valid cstate_rel
               apply (rule cDomScheduleIdx_to_H_correct)
               using cstate_rel
               apply (clarsimp simp: cstate_relation_def Let_def)
              using valid cstate_rel
              apply (rule cDomSchedule_to_H_correct)
              using cstate_rel
              apply (clarsimp simp: cstate_relation_def Let_def)
             using cstate_rel
             apply (clarsimp simp: cstate_relation_def Let_def ucast_up_ucast_id is_up_8_32)
            using cstate_rel
            apply (clarsimp simp: cstate_relation_def Let_def)
           apply (rule cready_queues_to_H_correct)
           using cstate_rel
           apply (clarsimp simp: cstate_relation_def Let_def)
          using cstate_rel
          apply (clarsimp simp: cstate_relation_def Let_def)
          using cstate_rel
          apply (clarsimp simp: cstate_relation_def Let_def)
          apply (rule cbitmap_L1_to_H_correct)
          apply (clarsimp simp: cstate_relation_def Let_def)
         using cstate_rel
         apply (clarsimp simp: cstate_relation_def Let_def)
         apply (rule cbitmap_L2_to_H_correct)
         apply (clarsimp simp: cstate_relation_def Let_def)
        using cstate_rel
        apply (clarsimp simp: cstate_relation_def Let_def)
       using cstate_rel
       apply (clarsimp simp: cstate_relation_def Let_def)
      using cstate_rel
      apply (clarsimp simp: cstate_relation_def Let_def)
      apply (rule csch_act_rel_to_H[THEN iffD1])
       apply (case_tac "ksSchedulerAction as", simp+)
       using valid
       subgoal
       by (clarsimp simp: valid_state'_def st_tcb_at'_def
                          obj_at'_real_def ko_wp_at'_def objBitsKO_def projectKO_opt_tcb
                       split: kernel_object.splits)
      using cstate_rel
      apply (clarsimp simp: cstate_relation_def Let_def)
     apply (rule cint_rel_to_H)
      using valid
      apply (simp add: valid_state'_def)
     using cstate_rel
     apply (clarsimp simp: cstate_relation_def Let_def)
    using cstate_rel
    apply (clarsimp simp: cstate_relation_def Let_def)
   apply (rule carch_state_to_H_correct)
     using valid
     apply (simp add: valid_state'_def)
    using cstate_rel
    apply (clarsimp simp: cstate_relation_def Let_def)
   using cstate_rel
   apply (clarsimp simp: cstate_relation_def Let_def carch_state_relation_def carch_globals_def)
  using cstate_rel
  apply (clarsimp simp: cstate_relation_def Let_def carch_state_relation_def carch_globals_def)
  apply (rule cstate_to_machine_H_correct[simplified])
      using valid
      apply (simp add: valid_state'_def)
     using cstate_rel
     apply (simp add: cstate_relation_def Let_def)
    using cstate_rel
    apply (simp add: cstate_relation_def Let_def cpspace_relation_def)
   using cstate_rel
   apply (simp add: cstate_relation_def Let_def cpspace_relation_def)
  using valid
  apply (clarsimp simp add: valid_state'_def)
  done

end

context state_rel begin

definition
  cstate_to_A :: "cstate \<Rightarrow> det_state"
where
  "cstate_to_A \<equiv> absKState \<circ> cstate_to_H \<circ> globals"

definition
  "Fin_C \<equiv> \<lambda>((tc,s),m,e). ((tc, cstate_to_A s),m,e)"

definition
  doUserOp_C
    :: "user_transition \<Rightarrow> user_context \<Rightarrow>
        (cstate, event option \<times> user_context) nondet_monad"
  where
  "doUserOp_C uop tc \<equiv>
   do t \<leftarrow> gets (ctcb_ptr_to_tcb_ptr \<circ> ksCurThread_' \<circ> globals);
      conv \<leftarrow> gets (ptable_lift t \<circ> cstate_to_A);
      rights \<leftarrow> gets (ptable_rights t \<circ> cstate_to_A);
      um \<leftarrow> gets (\<lambda>s. user_mem_C (globals s) \<circ> ptrFromPAddr);
      dm \<leftarrow> gets (\<lambda>s. device_mem_C (globals s) \<circ> ptrFromPAddr);
      ds \<leftarrow> gets (\<lambda>s. (device_state (phantom_machine_state_' (globals s))));

      assert (dom (um \<circ> addrFromPPtr) \<subseteq> - dom ds);
      assert (dom (dm \<circ> addrFromPPtr) \<subseteq> dom ds);

      (e,tc',um',ds') \<leftarrow> select (fst (uop t (restrict_map conv {pa. rights pa \<noteq> {}}) rights
                     (tc, restrict_map um
                          {pa. \<exists>va. conv va = Some pa \<and> AllowRead \<in> rights va},
                     (ds \<circ> ptrFromPAddr) |`  {pa. \<exists>va. conv va = Some pa \<and> AllowRead \<in> rights va} )));
      setUserMem_C ((um' |` {pa. \<exists>va. conv va = Some pa \<and> AllowWrite \<in> rights va}
                      \<circ> addrFromPPtr) |` (- dom ds));
      setDeviceState_C ((ds' |` {pa. \<exists>va. conv va = Some pa \<and> AllowWrite \<in> rights va}
                      \<circ> addrFromPPtr) |` (dom ds));
      return (e,tc')
   od"

definition
  do_user_op_C :: "user_transition \<Rightarrow>
                    ((user_context \<times> cstate) \<times> (event option \<times> user_context \<times> cstate)) set"
where
  "do_user_op_C uop \<equiv> monad_to_transition (doUserOp_C uop)"

end

context kernel_m begin

definition
  ADT_C :: "user_transition \<Rightarrow> (cstate global_state, det_ext observable, unit) data_type"
where
 "ADT_C uop \<equiv> \<lparr> Init = Init_C, Fin = Fin_C,
            Step = (\<lambda>u. global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C False)) \<rparr>"

definition
  ADT_FP_C :: "user_transition \<Rightarrow> (cstate global_state, det_ext observable, unit) data_type"
where
 "ADT_FP_C uop \<equiv> \<lparr> Init = Init_C, Fin = Fin_C,
               Step = (\<lambda>u. global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C True)) \<rparr>"

end

locale kernel_global = state_rel + kernel_all_global_addresses
(* repeating ADT definitions in the c-parser's locale now (not the substitute) *)
begin

definition
  "callKernel_C e \<equiv> case e of
    SyscallEvent n \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleSyscall(syscall_from_H n))
  | UnknownSyscall n \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleUnknownSyscall(of_nat n))
  | UserLevelFault w1 w2 \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleUserLevelFault(w1,w2))
  | Interrupt \<Rightarrow> exec_C \<Gamma> (Call handleInterruptEntry_'proc)
  | VMFaultEvent t \<Rightarrow> exec_C \<Gamma> (\<acute>ret__unsigned_long :== CALL handleVMFaultEvent(kernel_m.vm_fault_type_from_H t))
  | HypervisorEvent t \<Rightarrow> exec_C \<Gamma> handleHypervisorEvent_C"

definition
  "callKernel_withFastpath_C e \<equiv>
   if e = SyscallEvent syscall.SysCall \<or> e = SyscallEvent syscall.SysReplyRecv
   then exec_C \<Gamma> (\<acute>cptr :== CALL getRegister(\<acute>ksCurThread, scast Kernel_C.capRegister);;
                  \<acute>msgInfo :== CALL getRegister(\<acute>ksCurThread, scast Kernel_C.msgInfoRegister);;
                   IF e = SyscallEvent syscall.SysCall
                   THEN CALL fastpath_call(\<acute>cptr, \<acute>msgInfo)
                   ELSE CALL fastpath_reply_recv(\<acute>cptr, \<acute>msgInfo) FI)
   else callKernel_C e"

definition
  setTCBContext_C :: "user_context_C \<Rightarrow> tcb_C ptr \<Rightarrow> (cstate,unit) nondet_monad"
where
  "setTCBContext_C ct thread \<equiv>
  exec_C \<Gamma> (\<acute>t_hrs :== hrs_mem_update (heap_update (
    Ptr &((Ptr &(thread\<rightarrow>[''tcbArch_C'']) :: (arch_tcb_C ptr))\<rightarrow>[''tcbContext_C''])) ct) \<acute>t_hrs)"

definition
  "kernelEntry_C fp e tc \<equiv> do
    t \<leftarrow> gets (ksCurThread_' o globals);
    setTCBContext_C (to_user_context_C tc) t;
    if fp then callKernel_withFastpath_C e else callKernel_C e;
    t \<leftarrow> gets (ksCurThread_' o globals);
    gets $ getContext_C t
  od"

definition
  "kernel_call_C fp e \<equiv>
  {(s, m, s'). s' \<in> fst (split (kernelEntry_C fp e) s) \<and>
               m = (if ct_running_C (snd s') then UserMode else IdleMode)}"

definition
  "getActiveIRQ_C \<equiv> exec_C \<Gamma> (Call getActiveIRQ_'proc)"

definition
  "checkActiveIRQ_C \<equiv>
   do getActiveIRQ_C;
      irq \<leftarrow> gets ret__unsigned_long_';
      return (irq \<noteq> scast irqInvalid)
   od"

definition
  check_active_irq_C :: "((user_context \<times> cstate) \<times> bool \<times> (user_context \<times> cstate)) set"
  where
  "check_active_irq_C \<equiv> {((tc, s), irq_raised, (tc, s')). (irq_raised, s') \<in> fst (checkActiveIRQ_C s)}"

definition
  ADT_C :: "user_transition \<Rightarrow> (cstate global_state, det_ext observable, unit) data_type"
where
 "ADT_C uop \<equiv> \<lparr> Init = Init_C, Fin = Fin_C,
            Step = (\<lambda>u. global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C False)) \<rparr>"

definition
  ADT_FP_C :: "user_transition \<Rightarrow> (cstate global_state, det_ext observable, unit) data_type"
where
 "ADT_FP_C uop \<equiv> \<lparr> Init = Init_C, Fin = Fin_C,
               Step = (\<lambda>u. global_automaton check_active_irq_C (do_user_op_C uop) (kernel_call_C True)) \<rparr>"

end

end
