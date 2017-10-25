(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
The TCB and thread related specifications.
*)

chapter "Threads and TCBs"

theory Tcb_A
imports Schedule_A "$L4V_ARCH/ArchTcb_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_activate_idle_thread
  arch_tcb_set_ipc_buffer
  sanitise_register
  arch_get_sanitise_register_info
  arch_post_modify_registers

end

section "Activating Threads"

text {* Reactivate a thread if it is not already running. *}
definition
  restart :: "obj_ref \<Rightarrow> unit det_ext_monad" where
 "restart thread \<equiv> do
    state \<leftarrow> get_thread_state thread;
    sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
    when (\<not> runnable state \<and> \<not> idle state) $ do
      cancel_ipc thread;
      set_thread_state thread Restart;
      sc_ptr \<leftarrow> assert_opt sc_opt;
      do_extended_op (sched_context_resume sc_ptr);
      in_release_q \<leftarrow> gets $ in_release_queue thread;
      schedulable \<leftarrow> is_schedulable thread in_release_q;
      when schedulable $ possible_switch_to thread
    od
  od"

text {* This action is performed at the end of a system call immediately before
control is restored to a used thread. If it needs to be restarted then its
program counter is set to the operation it was performing rather than the next
operation. The idle thread is handled specially. *}
definition
  activate_thread :: "(unit, 'z::state_ext) s_monad" where
  "activate_thread \<equiv> do
     thread \<leftarrow> gets cur_thread;
     state \<leftarrow> get_thread_state thread;
     (case state
       of Running \<Rightarrow> return ()
        | YieldTo _ \<Rightarrow> complete_yield_to thread
        | Restart \<Rightarrow> (do
            pc \<leftarrow> as_user thread getRestartPC;
            as_user thread $ setNextPC pc;
            set_thread_state thread Running
          od)
        | IdleThreadState \<Rightarrow> arch_activate_idle_thread thread
        | _ \<Rightarrow> fail)
   od"

section "Thread Message Formats"

definition
  load_word_offs :: "obj_ref \<Rightarrow> nat \<Rightarrow> (machine_word,'z::state_ext) s_monad" where
 "load_word_offs ptr offs \<equiv>
    do_machine_op $ loadWord (ptr + of_nat (offs * word_size))"
definition
  load_word_offs_word :: "obj_ref \<Rightarrow> data \<Rightarrow> (machine_word,'z::state_ext) s_monad" where
 "load_word_offs_word ptr offs \<equiv>
    do_machine_op $ loadWord (ptr + (offs * word_size))"

text {* Copy message registers from one thread to another. *}
definition
  copy_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref \<Rightarrow>
               obj_ref option \<Rightarrow> length_type \<Rightarrow> (length_type,'z::state_ext) s_monad" where
  "copy_mrs sender sbuf receiver rbuf n \<equiv>
   do
     hardware_mrs \<leftarrow> return $ take (unat n) msg_registers;
     mapM (\<lambda>r. do
         v \<leftarrow> as_user sender $ get_register r;
         as_user receiver $ set_register r v
       od) hardware_mrs;
     buf_mrs \<leftarrow> case (sbuf, rbuf) of
       (Some sb_ptr, Some rb_ptr) \<Rightarrow> mapM (\<lambda>x. do
                                       v \<leftarrow> load_word_offs sb_ptr x;
                                       store_word_offs rb_ptr x v
                                     od)
               [length msg_registers + 1 ..< Suc (unat n)]
     | _ \<Rightarrow> return [];
     return $ min n $ nat_to_len $ length hardware_mrs + length buf_mrs
   od"

text {* The ctable and vtable slots of the TCB. *}
definition
  get_tcb_ctable_ptr :: "obj_ref \<Rightarrow> cslot_ptr" where
  "get_tcb_ctable_ptr tcb_ref \<equiv> (tcb_ref, tcb_cnode_index 0)"

definition
  get_tcb_vtable_ptr :: "obj_ref \<Rightarrow> cslot_ptr" where
  "get_tcb_vtable_ptr tcb_ref \<equiv> (tcb_ref, tcb_cnode_index 1)"

text {* Optionally update the tcb at an address. *}
definition
  option_update_thread :: "obj_ref \<Rightarrow> ('a \<Rightarrow> tcb \<Rightarrow> tcb) \<Rightarrow> 'a option \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "option_update_thread thread fn \<equiv> case_option (return ()) (\<lambda>v. thread_set (fn v) thread)"

text {* Check that a related capability is at an address. This is done before
calling @{const cap_insert} to avoid a corner case where the would-be parent of
the cap to be inserted has been moved or deleted. *}
definition
  check_cap_at :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "check_cap_at cap slot m \<equiv> do
    cap' \<leftarrow> get_cap slot;
    when (same_object_as cap cap') m
  od"


text {* Helper function for binding notifications *}
definition
  bind_notification :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "bind_notification tcbptr ntfnptr \<equiv> do
     set_ntfn_obj_ref ntfn_bound_tcb_update ntfnptr $ Some tcbptr;
     set_tcb_obj_ref tcb_bound_notification_update tcbptr $ Some ntfnptr
   od"

definition
  install_tcb_cap :: "obj_ref \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> nat \<Rightarrow> (cap \<times> cslot_ptr) option \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
  "install_tcb_cap target tcap slot n slot_opt \<equiv> (* do we need tcap?; tcap = ThreadCap target *)
     case slot_opt of None \<Rightarrow> returnOk ()
     | Some (new_cap, src_slot) \<Rightarrow> doE
      cap_delete (target, tcb_cnode_index n);
      liftE $ check_cap_at new_cap src_slot
            $ check_cap_at tcap slot
            $ cap_insert new_cap src_slot (target, tcb_cnode_index n)
    odE"

text {* TCB capabilities confer authority to perform seven actions. A thread can
request to yield its timeslice to another, to suspend or resume another, to
reconfigure another thread, or to copy register sets into, out of or between
other threads. *}
fun
  invoke_tcb :: "tcb_invocation \<Rightarrow> (data list, 'z::state_ext) p_monad"
where
  "invoke_tcb (Suspend thread) = liftE (do suspend thread; return [] od)"
| "invoke_tcb (Resume thread) = liftE (do do_extended_op $ restart thread; return [] od)"

| "invoke_tcb (ThreadControl target slot fault_handler timeout_handler mcp priority croot vroot buffer sc)
   = doE
    liftE $  case mcp of None \<Rightarrow> return()
     | Some (newmcp, _) \<Rightarrow> set_mcpriority target newmcp;
    liftE $ case priority of None \<Rightarrow> return()
     | Some (prio, _) \<Rightarrow> do_extended_op (set_priority target prio);
    liftE $ case sc of None \<Rightarrow> return ()
     | Some None \<Rightarrow> do
       sc_ptr_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
       maybeM sched_context_unbind_tcb sc_ptr_opt
     od
     | Some (Some sc_ptr) \<Rightarrow> do
        sc' \<leftarrow> get_tcb_obj_ref tcb_sched_context target;
        when (sc' \<noteq> Some sc_ptr) $ do_extended_op $ sched_context_bind_tcb sc_ptr target
     od;
    install_tcb_cap target (ThreadCap target) slot 0 croot;
    install_tcb_cap target (ThreadCap target) slot 1 vroot;
    install_tcb_cap target (ThreadCap target) slot 3 fault_handler;
    install_tcb_cap target (ThreadCap target) slot 4 timeout_handler;
    (case buffer of None \<Rightarrow> returnOk ()
     | Some (ptr, frame) \<Rightarrow> doE
      cap_delete (target, tcb_cnode_index 2);
      liftE $ thread_set (\<lambda>t. t \<lparr> tcb_ipc_buffer := ptr \<rparr>) target;
      liftE $ arch_tcb_set_ipc_buffer target ptr;
      liftE $ case frame of None \<Rightarrow> return ()
       | Some (new_cap, src_slot) \<Rightarrow>
            check_cap_at new_cap src_slot
          $ check_cap_at (ThreadCap target) slot
          $ cap_insert new_cap src_slot (target, tcb_cnode_index 2);
      cur \<leftarrow> liftE $ gets cur_thread;
      liftE $ when (target = cur) (do_extended_op reschedule_required)
    odE);
    returnOk []
  odE"

| "invoke_tcb (CopyRegisters dest src suspend_source resume_target transfer_frame transfer_integer transfer_arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    when resume_target $ do_extended_op $ restart dest;
    when transfer_frame $ do
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) frame_registers;
        pc \<leftarrow> as_user dest getRestartPC;
        as_user dest $ setNextPC pc
    od;
    when transfer_integer $
        mapM_x (\<lambda>r. do
                v \<leftarrow> as_user src $ getRegister r;
                as_user dest $ setRegister r v
        od) gpRegisters;
    cur \<leftarrow> gets cur_thread;
    arch_post_modify_registers cur dest;
    when (dest = cur) (do_extended_op reschedule_required);
    return []
  od)"

| "invoke_tcb (ReadRegisters src suspend_source n arch) =
  (liftE $ do
    when suspend_source $ suspend src;
    self \<leftarrow> gets cur_thread;
    regs \<leftarrow> return (take (unat n) $ frame_registers @ gp_registers);
    as_user src $ mapM getRegister regs
  od)"

| "invoke_tcb (WriteRegisters dest resume_target values arch) =
  (liftE $ do
    self \<leftarrow> gets cur_thread;
    b \<leftarrow> arch_get_sanitise_register_info dest;
    as_user dest $ do
        zipWithM (\<lambda>r v. setRegister r (sanitise_register b r v))
            (frameRegisters @ gpRegisters) values;
        pc \<leftarrow> getRestartPC;
        setNextPC pc
    od;
    arch_post_modify_registers self dest;
    when resume_target $ do_extended_op $ restart dest;
    when (dest = self) (do_extended_op reschedule_required);
    return []
  od)"

| "invoke_tcb (NotificationControl tcb (Some ntfnptr)) =
  (liftE $ do
    bind_notification tcb ntfnptr;
    return []
  od)"

| "invoke_tcb (NotificationControl tcb None) =
  (liftE $ do
    unbind_notification tcb;
    return []
  od)"

definition
  set_domain :: "obj_ref \<Rightarrow> domain \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "set_domain tptr new_dom \<equiv> do
     cur \<leftarrow> gets cur_thread;
     do_extended_op $ tcb_sched_action tcb_sched_dequeue tptr;
     do_extended_op $ thread_set_domain tptr new_dom;
     ts \<leftarrow> get_thread_state tptr;
     when (runnable ts) $ do_extended_op $ (tcb_sched_action tcb_sched_enqueue tptr);
     when (tptr = cur) $ do_extended_op $ reschedule_required
   od"

definition invoke_domain:: "obj_ref \<Rightarrow> domain \<Rightarrow> (data list,'z::state_ext) p_monad"
where
  "invoke_domain thread domain \<equiv>
     liftE (do do_extended_op (set_domain thread domain); return [] od)"

text {* Get all of the message registers, both from the sending thread's current
register file and its IPC buffer. *}
definition
  get_mrs :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> message_info \<Rightarrow>
              (message list,'z::state_ext) s_monad" where
  "get_mrs thread buf info \<equiv> do
     context \<leftarrow> thread_get (arch_tcb_context_get o tcb_arch) thread;
     cpu_mrs \<leftarrow> return (map context msg_registers);
     buf_mrs \<leftarrow> case buf
       of None      \<Rightarrow> return []
        | Some pptr \<Rightarrow> mapM (\<lambda>x. load_word_offs pptr x)
               [length msg_registers + 1 ..< Suc msg_max_length];
     return (take (unat (mi_length info)) $ cpu_mrs @ buf_mrs)
   od"

end
