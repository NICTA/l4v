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
Non-deterministic scheduler functionality.
*)

chapter "Scheduler"

theory Schedule_A
imports "./$L4V_ARCH/Arch_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_switch_to_thread
  arch_switch_to_idle_thread

end

abbreviation
  "idle st \<equiv> st = Structures_A.IdleThreadState"

text {* Gets the TCB at an address if the thread can be scheduled. *}
definition
  getActiveTCB :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> tcb option"
where
  "getActiveTCB tcb_ref state \<equiv>
   case (get_tcb tcb_ref state)
     of None           \<Rightarrow> None
      | Some tcb       \<Rightarrow> if (schedulable tcb) then Some tcb else None"

text {* Gets all schedulable threads in the system. *}
definition
  allActiveTCBs :: "(obj_ref set,'z::state_ext) s_monad" where
  "allActiveTCBs \<equiv> do
    state \<leftarrow> get;
    return {x. getActiveTCB x state \<noteq> None}
   od"

text {* Switches the current thread to the specified one. *}
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);
     arch_switch_to_thread t;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) t);
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text {* Asserts that a thread is schedulable before switching to it. *}
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"guarded_switch_to thread \<equiv> do sched \<leftarrow> thread_get schedulable thread;
                    assert sched;
                    switch_to_thread thread
                 od"

text {* Switches to the idle thread. *}
definition
  switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
  "switch_to_idle_thread \<equiv> do
     thread \<leftarrow> gets idle_thread;
     arch_switch_to_idle_thread;
     modify (\<lambda>s. s \<lparr> cur_thread := thread \<rparr>)
   od"

definition
  end_timeslice :: "(unit,'z::state_ext) s_monad"
where
  "end_timeslice = do
     cur \<leftarrow> gets cur_thread;
     tcb \<leftarrow> gets_the $ get_tcb cur;
     sc_ptr \<leftarrow> return $ the (tcb_sched_context tcb);
     recharge sc_ptr;
     st \<leftarrow> get_thread_state cur;
     when (st = Running) (do_extended_op $ tcb_sched_action tcb_sched_append cur);
     do_extended_op reschedule_required
  od"

definition
  set_next_interrupt :: "(unit, 'z::state_ext) s_monad"
where
  "set_next_interrupt = do
     cur_tm \<leftarrow> gets cur_time;
     cur_th \<leftarrow> gets cur_thread;
     tcb \<leftarrow> gets_the $ get_tcb cur_th;
     sc \<leftarrow> get_sched_context $ the (tcb_sched_context tcb);
     new_thread_time \<leftarrow> return (cur_tm + sc_remaining sc);
     do_extended_op $ set_next_timer_interrupt new_thread_time
  od"

definition
  check_budget :: "(bool, 'z::state_ext) s_monad"
where
  "check_budget = do
    cur_exp \<leftarrow> is_cur_thread_expired;
    cur_sc \<leftarrow> gets_the cur_sc;
    if cur_exp then do
      commit_time cur_sc;
      end_timeslice;
      return False
    od
    else do
      dom_exp \<leftarrow> select_ext is_cur_domain_expired {True,False};
      if dom_exp then do
        commit_time cur_sc;
        do_extended_op reschedule_required;
        return False
      od
      else return True
    od
  od"

definition
  check_budget_restart :: "(bool, 'z::state_ext) s_monad"
where
  "check_budget_restart = do
     cont \<leftarrow> check_budget;
     when (\<not>cont) $ do
       cur \<leftarrow> gets cur_thread;
       set_thread_state cur Restart
     od;
     return cont
  od"

definition
  check_reschedule :: "(unit,'z::state_ext) s_monad"
where
  "check_reschedule = do
     expired \<leftarrow> is_cur_thread_expired;
     if expired then end_timeslice
     else do
       dom_exp \<leftarrow> select_ext is_cur_domain_expired {True,False};
       when dom_exp (do_extended_op reschedule_required)
     od
   od"

definition
  switch_sched_context :: "(unit,'z::state_ext) s_monad"
where
  "switch_sched_context = do
    cur_sc \<leftarrow> gets cur_sc;
    cur_th \<leftarrow> gets cur_thread;
    tcb \<leftarrow> gets_the $ get_tcb cur_th;
    if cur_sc \<noteq> tcb_sched_context tcb
    then do
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
      commit_time (the cur_sc)
    od
    else
      rollback_time;
    modify (\<lambda>s. s\<lparr> cur_sc:= tcb_sched_context tcb \<rparr>)
  od"

definition
  sc_and_timer :: "(unit, 'z::state_ext) s_monad"
where
  "sc_and_timer = do
    switch_sched_context;
    reprogram \<leftarrow> gets reprogram_timer;
    when reprogram $ do
      set_next_interrupt;
      modify (\<lambda>s. s\<lparr>reprogram_timer:= False\<rparr>)
    od
  od"


class state_ext_sched = state_ext +
  fixes schedule :: "(unit,'a) s_monad"

definition choose_thread :: "det_ext state \<Rightarrow> (unit \<times> det_ext state) set \<times> bool" where
"choose_thread \<equiv>
      do
        d \<leftarrow> gets cur_domain;
        queues \<leftarrow> gets (\<lambda>s. ready_queues s d);
        if (\<forall>prio. queues prio = []) then (switch_to_idle_thread)
        else (guarded_switch_to (hd (max_non_empty_queue queues)))
      od"

text {*
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready. *}
definition
  is_highest_prio :: "domain \<Rightarrow> priority \<Rightarrow> det_ext state \<Rightarrow> bool"
where
  "is_highest_prio d p s \<equiv>
    (\<forall>prio. ready_queues s d prio = [])
    \<or> p \<ge> Max {prio. ready_queues s d prio \<noteq> []}"

instantiation  det_ext_ext :: (type) state_ext_sched
begin

definition
  "schedule_switch_thread_fastfail ct it ct_prio target_prio \<equiv>
     if ct \<noteq> it
     then return (target_prio < ct_prio)
     else return True"

definition
  "schedule_choose_new_thread \<equiv> do
     dom_time \<leftarrow> gets domain_time;
     when (dom_time = 0) next_domain;
     choose_thread;
     set_scheduler_action resume_cur_thread
   od"

definition
  "schedule_det_ext_ext \<equiv> do
     ct \<leftarrow> gets cur_thread;
     ct_st \<leftarrow> get_thread_state ct;
     ct_schedulable \<leftarrow> thread_get schedulable ct;
     action \<leftarrow> gets scheduler_action;
     (case action
       of resume_cur_thread \<Rightarrow> do
            id \<leftarrow> gets idle_thread;
            assert (ct_schedulable \<or> ct = id);
            return ()
         od
       | choose_new_thread \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_schedulable (tcb_sched_action tcb_sched_enqueue ct);

           it \<leftarrow> gets idle_thread;
           target_prio \<leftarrow> ethread_get tcb_priority candidate;

           (* Infoflow does not like asking about the idle thread's priority or domain. *)
           ct_prio \<leftarrow> ethread_get_when (ct \<noteq> it) tcb_priority ct;
           (* When to look at the bitmaps.
              This optimisation used in C fast path, but there we know cur_thread is not idle. *)
           fastfail \<leftarrow> schedule_switch_thread_fastfail ct it ct_prio target_prio;

           cur_dom \<leftarrow> gets cur_domain;
           highest \<leftarrow> gets (is_highest_prio cur_dom target_prio);
           if (fastfail \<and> \<not>highest)
           then do
               (* candidate is not best candidate, choose a new thread *)
               tcb_sched_action tcb_sched_enqueue candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else if (ct_schedulable \<and> ct_prio = target_prio)
           then do
               (* current thread was runnable and candidate is not strictly better
                  want current thread to run next, so append the candidate to end of queue
                  and choose again *)
               tcb_sched_action tcb_sched_append candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else do
             guarded_switch_to candidate;
             (* duplication assists in wp proof under different sched. actions *)
             set_scheduler_action resume_cur_thread
           od
        od);
     sc_and_timer
    od"

instance ..
end


instantiation unit :: state_ext_sched
begin


text {*
  The scheduler is heavily underspecified.
  It is allowed to pick any active thread or the idle thread.
  If the thread the scheduler picked is the current thread, it
  may omit the call to @{const switch_to_thread}. Likewise it
  may omit the call to @{const switch_to_idle_thread} if the
  idle thread is the current thread.
*}
definition schedule_unit :: "(unit,unit) s_monad" where
"schedule_unit \<equiv> do
 (do
   cur \<leftarrow> gets cur_thread;
   threads \<leftarrow> allActiveTCBs;
   thread \<leftarrow> select threads;
   (if thread = cur then
     return () \<sqinter> switch_to_thread thread
   else
     switch_to_thread thread)
 od) \<sqinter>
 (do
   cur \<leftarrow> gets cur_thread;
   idl \<leftarrow> gets idle_thread;
   if idl = cur then
     return () \<sqinter> switch_to_idle_thread
   else switch_to_idle_thread
  od);
  sc_and_timer
  od"

instance ..
end


lemmas schedule_def = schedule_det_ext_ext_def schedule_unit_def

end
