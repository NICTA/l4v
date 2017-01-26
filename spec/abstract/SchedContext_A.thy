(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Scheduling Contexts and Control"

theory SchedContext_A
imports KHeap_A Invocations_A
begin

text \<open> This theory contains operations on scheduling contexts and scheduling control. \<close>


text \<open> Replenish remaining time in scheduling context \<close>
definition
  recharge :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "recharge sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    assert (0 < sc_budget sc);
    sc' \<leftarrow> return $ sc\<lparr>sc_remaining := sc_budget sc\<rparr>;
    set_sched_context sc_ptr sc'
  od"

text \<open>
  Resume a scheduling context: check if the bound TCB
  is runnable and add it to the scheduling queue if required
\<close> 
definition
  sched_context_resume :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_resume sc_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> return $ the $ sc_tcb sc;
     ts \<leftarrow> thread_get tcb_state tptr;
     when (runnable ts \<and> 0 < sc_budget sc) $ do
        recharge sc_ptr;
        do_extended_op $ switch_if_required_to tptr
    od
  od"


text \<open>  Bind a TCB to a scheduling context. \<close>
definition
  sched_context_bind :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_bind sc_ptr tcb_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_tcb := Some tcb_ptr\<rparr>);
    thread_set (\<lambda>tcb. tcb\<lparr>tcb_sched_context := Some sc_ptr\<rparr>) tcb_ptr; 
    sched_context_resume sc_ptr
  od"


text \<open>
  Unbind a TCB from its scheduling context. If the TCB is runnable,
  remove from the scheduler.
\<close>
definition
  sched_context_unbind :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind sc_ptr = do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> return $ the $ sc_tcb sc;
     do_extended_op $ tcb_sched_action tcb_sched_dequeue tptr;
     thread_set (\<lambda>tcb. tcb \<lparr> tcb_sched_context := None \<rparr>) tptr;
     cur \<leftarrow> gets $ cur_thread;
     when (tptr = cur) $ do_extended_op reschedule_required
  od"

text \<open> Unbind TCB, if there is one bound. \<close>
definition
  sched_context_unbind_all_tcbs :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_unbind_all_tcbs sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    when (sc_tcb sc \<noteq> None) $ sched_context_unbind sc_ptr
  od"

text \<open> Unbind TCB from its scheduling context, if there is one bound. \<close>
definition
  unbind_from_sc :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "unbind_from_sc tcb_ptr = do
    sc_ptr_opt \<leftarrow> thread_get tcb_sched_context tcb_ptr;
    when (sc_ptr_opt \<noteq> None) $ sched_context_unbind (the sc_ptr_opt)
  od"


text \<open> User-level scheduling context invocations. \<close>
definition
  invoke_sched_context :: "sched_context_invocation \<Rightarrow> (unit, 'z::state_ext) se_monad"
where
  "invoke_sched_context iv \<equiv> liftE $ case iv of
    InvokeSchedContextBind sc_ptr tcb_ptr \<Rightarrow> sched_context_bind sc_ptr tcb_ptr 
  | InvokeSchedContextUnbindObject sc_ptr \<Rightarrow> sched_context_unbind sc_ptr
  | InvokeSchedContextUnbind sc_ptr \<Rightarrow> sched_context_unbind_all_tcbs sc_ptr"


text \<open> The Scheduling Control invocation configures the budget of a scheduling context. \<close>
definition
  invoke_sched_control_configure :: "sched_control_invocation \<Rightarrow> (unit, 'z::state_ext) se_monad"
where
  "invoke_sched_control_configure iv \<equiv>
  case iv of InvokeSchedControlConfigure sc_ptr budget \<Rightarrow> liftE $ do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_budget:= budget\<rparr>);
    recharge sc_ptr;
    when (sc_tcb sc \<noteq> None) $ do
      tcb_ptr \<leftarrow> return $ the (sc_tcb sc);
      tcb \<leftarrow> thread_get id tcb_ptr;
      do_extended_op $ schedule_tcb tcb_ptr tcb;
      if \<not>schedulable tcb then
        do_extended_op $ tcb_sched_action tcb_sched_dequeue tcb_ptr
      else
        do_extended_op $ switch_if_required_to tcb_ptr
    od
  od"

end
