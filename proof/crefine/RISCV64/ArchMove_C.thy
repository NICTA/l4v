(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before CRefine *)

theory ArchMove_C
imports "../Move_C"
begin

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

lemma unat_mask_3_less_8:
  "unat (p && mask 3 :: word64) < 8"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

definition
  user_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "user_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInUserData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"
definition
  device_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "device_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInDeviceData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"

(* FIXME: move to GenericLib *)
lemmas unat64_eq_of_nat = unat_eq_of_nat[where 'a=64, folded word_bits_def]

context begin interpretation Arch .

(* FIXME RISCV: some 64-bit lemmas from X64's ArchMove_C will be needed here *)

crunch inv'[wp]: archThreadGet P

(* FIXME MOVE near thm tg_sp' *)
lemma atg_sp':
  "\<lbrace>P\<rbrace> archThreadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f (tcbArch t') = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: archThreadGet_def)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

(* FIXME: MOVE to EmptyFail *)
lemma empty_fail_archThreadGet [intro!, wp, simp]:
  "empty_fail (archThreadGet f p)"
  by (simp add: archThreadGet_def getObject_def split_def)

(* FIXME: move to ainvs? *)
lemma sign_extend_canonical_address:
  "(x = sign_extend 38 x) = canonical_address x"
  by (fastforce simp: sign_extended_iff_sign_extend canonical_address_sign_extended canonical_bit_def)

lemma ptr_range_mask_range:
  "{ptr..ptr + 2 ^ bits - 1} = mask_range ptr bits"
  unfolding mask_def
  by simp

lemma valid_untyped':
  notes usableUntypedRange.simps[simp del]
  assumes pspace_distinct': "pspace_distinct' s" and
           pspace_aligned': "pspace_aligned' s" and
                        al: "is_aligned ptr bits"
  shows "valid_untyped' d ptr bits idx s =
         (\<forall>p ko. ksPSpace s p = Some ko \<longrightarrow>
                 obj_range' p ko \<inter> {ptr..ptr + 2 ^ bits - 1} \<noteq> {} \<longrightarrow>
                 obj_range' p ko \<subseteq> {ptr..ptr + 2 ^ bits - 1} \<and>
                 obj_range' p ko \<inter>
                   usableUntypedRange (UntypedCap d ptr bits idx) = {})"
  apply (simp add: valid_untyped'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule arg_cong[where f=All])
  apply (rule ext)
  apply (rule arg_cong[where f=All])
  apply (rule ext)
  apply (case_tac "ksPSpace s ptr' = Some ko", simp_all)
  apply (frule pspace_alignedD'[OF _ pspace_aligned'])
  apply (frule pspace_distinctD'[OF _ pspace_distinct'])
  apply (simp add: ptr_range_mask_range)
  apply (frule aligned_ranges_subset_or_disjoint[OF al])
  apply (simp only: ptr_range_mask_range)
  apply (fold obj_range'_def)
  apply (rule iffI)
   apply auto[1]
  apply (rule conjI)
   apply (rule ccontr, simp)
   apply (simp add: Set.psubset_eq)
   apply (erule conjE)
   apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp)
   apply (cut_tac is_aligned_no_overflow[OF al])
   apply (clarsimp simp add: obj_range'_def mask_def add_diff_eq)
   subgoal by auto
  apply (clarsimp simp add: usableUntypedRange.simps Int_commute)
  apply (case_tac "obj_range' ptr' ko \<inter> mask_range ptr bits \<noteq> {}", simp+)
  apply (cut_tac is_aligned_no_overflow[OF al])
  apply (clarsimp simp add: obj_range'_def mask_def add_diff_eq)
  apply (frule is_aligned_no_overflow)
  by (metis al intvl_range_conv' le_m1_iff_lt less_is_non_zero_p1
               nat_le_linear power_overflow sub_wrap add_0
               add_0_right word_add_increasing word_less_1 word_less_sub_1)

lemma more_pageBits_inner_beauty:
  fixes x :: "9 word"
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pageBits >> 3)"
  shows "(p && ~~ mask pageBits) + (ucast x * 8) \<noteq> p"
  apply clarsimp
  apply (simp add: word_shift_by_3)
  apply (subst (asm) word_plus_and_or_coroll)
   apply (clarsimp simp: word_size word_ops_nth_size nth_ucast
                         nth_shiftl bang_eq)
   apply (drule test_bit_size)
   apply (clarsimp simp: word_size pageBits_def)
   apply arith
  apply (insert x)
  apply (erule notE)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr bang_eq)
  apply (erule_tac x="n+3" in allE)
  apply (clarsimp simp: word_ops_nth_size word_size)
  apply (clarsimp simp: pageBits_def)
  done

(* FIXME x64: figure out where these are needed and adjust appropriately *)
lemma mask_pageBits_inner_beauty:
  "is_aligned p 3 \<Longrightarrow>
  (p && ~~ mask pageBits) + (ucast ((ucast (p && mask pageBits >> 3)):: 9 word) * 8) = (p::machine_word)"
  apply (simp add: is_aligned_nth word_shift_by_3)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size word_ops_nth_size nth_ucast nth_shiftr nth_shiftl
                        pageBits_def)
  apply (rule iffI)
   apply (erule disjE)
    apply clarsimp
   apply clarsimp
  apply simp
  apply clarsimp
  apply (rule context_conjI)
   apply (rule leI)
   apply clarsimp
  apply simp
  apply arith
  done

lemmas mask_64_id[simp] = mask_len_id[where 'a=64, folded word_bits_def]
                          mask_len_id[where 'a=64, simplified]

lemma prio_ucast_shiftr_wordRadix_helper: (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) < 4"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper': (* FIXME generalise *)
  "(ucast (p::priority) >> wordRadix :: machine_word) \<le> 3"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_unat_shiftr_wordRadix_helper': (* FIXME generalise *)
  "unat ((p::priority) >> wordRadix) \<le> 3"
  unfolding maxPriority_def numPriorities_def wordRadix_def
  using unat_lt2p[where x=p]
  apply (clarsimp simp add: word_less_nat_alt shiftr_div_2n' unat_ucast_upcast is_up word_le_nat_alt)
  apply arith
  done

lemma prio_ucast_shiftr_wordRadix_helper2: (* FIXME possibly unused *)
  "(ucast (p::priority) >> wordRadix :: machine_word) < 0x20"
  by (rule order_less_trans[OF prio_ucast_shiftr_wordRadix_helper]; simp)

lemma prio_ucast_shiftr_wordRadix_helper3:
  "(ucast (p::priority) >> wordRadix :: machine_word) < 0x40"
  by (rule order_less_trans[OF prio_ucast_shiftr_wordRadix_helper]; simp)

lemma unat_ucast_prio_L1_cmask_simp:
  "unat (ucast (p::priority) && 0x3F :: machine_word) = unat (p && 0x3F)"
  using unat_ucast_prio_mask_simp[where m=6]
  by (simp add: mask_def)

lemma machine_word_and_3F_less_40:
  "(w :: machine_word) && 0x3F < 0x40"
  by (rule word_and_less', simp)

lemmas setEndpoint_obj_at_tcb' = setEndpoint_obj_at'_tcb

(* FIXME: Move to Schedule_R.thy. Make Arch_switchToThread_obj_at a specialisation of this *)
lemma Arch_switchToThread_obj_at_pre:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   Arch.switchToThread t
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: RISCV64_H.switchToThread_def)
  apply (wp asUser_obj_at_notQ doMachineOp_obj_at hoare_drop_imps|wpc)+
  done

lemma loadWordUser_submonad_fn:
  "loadWordUser p = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                (pointerInUserData p) (loadWord p)"
  by (simp add: loadWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma storeWordUser_submonad_fn:
  "storeWordUser p v = submonad_fn ksMachineState (ksMachineState_update \<circ> K)
                                   (pointerInUserData p) (storeWord p v)"
  by (simp add: storeWordUser_def submonad_doMachineOp.fn_is_sm submonad_fn_def)

lemma threadGet_tcbFault_loadWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> loadWordUser p; n x y od =
   do y \<leftarrow> loadWordUser p; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                loadWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply (simp add: ef_loadWord)
  done

lemma threadGet_tcbFault_storeWordUser_comm:
  "do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> storeWordUser p v; n x y od =
   do y \<leftarrow> storeWordUser p v; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm [OF tcbFault_submonad_args _
                                threadGet_tcbFault_submonad_fn
                                storeWordUser_submonad_fn])
       apply (simp add: submonad_args_def pointerInUserData_def)
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (clarsimp simp: thread_replace_def Let_def typ_at'_def ko_wp_at'_def
                          ps_clear_upd ps_clear_upd_None pointerInUserData_def
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply (simp add: ef_storeWord)
  done

lemma asUser_getRegister_discarded:
  "(asUser t (getRegister r)) >>= (\<lambda>_. n) =
   stateAssert (tcb_at' t) [] >>= (\<lambda>_. n)"
  apply (rule ext)
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def
                        submonad_asUser.args assert_def select_f_def
                        gets_def get_def modify_def put_def
                        getRegister_def bind_def split_def
                        return_def fail_def stateAssert_def)
  done

crunch pspace_canonical'[wp]: setThreadState pspace_canonical'

lemma obj_at_kernel_mappings':
  "\<lbrakk>pspace_in_kernel_mappings' s; obj_at' P p s\<rbrakk>
   \<Longrightarrow> p \<in> kernel_mappings"
  by (clarsimp simp: pspace_in_kernel_mappings'_def obj_at'_def dom_def)

crunches Arch.switchToThread
  for valid_queues'[wp]: valid_queues'
  (simp: crunch_simps wp: hoare_drop_imps)
crunches switchToIdleThread
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
crunches switchToIdleThread, switchToThread
  for valid_pspace'[wp]: valid_pspace'
  (simp: whenE_def crunch_simps wp: hoare_drop_imps)

end

end
