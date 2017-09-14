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
  "getActiveTCB tcb_ref s \<equiv>
   case get_tcb tcb_ref s
     of None     \<Rightarrow> None
      | Some tcb \<Rightarrow> if is_schedulable_opt tcb_ref False s = Some True then Some tcb else None"

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
definition guarded_switch_to :: "obj_ref \<Rightarrow> unit det_ext_monad" where
  "guarded_switch_to thread \<equiv> do
     inq \<leftarrow> gets $ in_release_queue thread;
     sched \<leftarrow> is_schedulable thread inq;
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
     sc_ptr \<leftarrow> gets_the cur_sc;
     ready \<leftarrow> refill_ready sc_ptr;
     sufficient \<leftarrow> refill_sufficient sc_ptr 0;
     if ready \<and> sufficient then do
       cur \<leftarrow> gets cur_thread;
       do_extended_op $ tcb_sched_action tcb_sched_append cur
     od
     else
       postpone sc_ptr
  od"

definition
  set_next_interrupt :: "unit det_ext_monad"
where
  "set_next_interrupt = do
     cur_tm \<leftarrow> gets cur_time;
     cur_th \<leftarrow> gets cur_thread;
     sc_opt \<leftarrow> thread_get tcb_sched_context cur_th;
     sc_ptr \<leftarrow> assert_opt sc_opt;
     sc \<leftarrow> get_sched_context sc_ptr;
     new_thread_time \<leftarrow> return $ cur_tm + r_amount (refill_hd sc);
     rq \<leftarrow> gets release_queue;
     new_thread_time \<leftarrow> if rq = [] then return new_thread_time else do
       sc_opt \<leftarrow> thread_get tcb_sched_context (hd rq);
       sc_ptr \<leftarrow> assert_opt sc_opt;
       sc \<leftarrow> get_sched_context sc_ptr;
       return $ min (r_time (refill_hd sc)) new_thread_time
     od;
     set_next_timer_interrupt new_thread_time
  od"

definition
  check_budget :: "bool det_ext_monad"
where
  "check_budget = do
    ct \<leftarrow> gets cur_thread;
    it \<leftarrow> gets idle_thread;
    if ct = it then return True else do
      csc \<leftarrow> gets_the cur_sc;
      consumed \<leftarrow> gets consumed_time;
      capacity \<leftarrow> refill_capacity csc consumed;
      if capacity < MIN_BUDGET then do
        when (capacity = 0) $ do
          cs' \<leftarrow> refill_budget_check csc consumed;
          modify $ consumed_time_update (K cs')
        od;
        consumed \<leftarrow> gets consumed_time;
        when (0 < consumed) $ refill_split_check csc consumed;
        modify $ consumed_time_update (K 0);
        st \<leftarrow> get_thread_state ct;
        when (runnable st) $ do
          end_timeslice;
          reschedule_required
        od;
        return False
      od
      else do
        dom_exp \<leftarrow> gets is_cur_domain_expired;
        if dom_exp then do
          commit_time;
          reschedule_required;
          return False
        od
        else return True
      od
    od
  od"

definition
  check_budget_restart :: "bool det_ext_monad"
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
  switch_sched_context :: "(unit,'z::state_ext) s_monad"
where
  "switch_sched_context = do
    cur_sc \<leftarrow> gets cur_sc;
    cur_th \<leftarrow> gets cur_thread;
    tcb \<leftarrow> gets_the $ get_tcb cur_th;
    if cur_sc \<noteq> tcb_sched_context tcb
    then do
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>);
      commit_time;
      refill_unblock_check (the (tcb_sched_context tcb))
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
      do_extended_op set_next_interrupt;
      modify (\<lambda>s. s\<lparr>reprogram_timer:= False\<rparr>)
    od
  od"

definition
  fun_of_m :: "('s, 'a) nondet_monad \<Rightarrow> 's \<Rightarrow> 'a option"
where
  "fun_of_m m \<equiv> \<lambda>s. if \<exists>x s'. m s = ({(x,s')}, False)
                    then Some (THE x. \<exists>s'. m s = ({(x,s')}, False))
                    else None"

definition
  refill_ready_tcb :: "obj_ref \<Rightarrow> bool det_ext_monad"
where
  "refill_ready_tcb t = do
     sc_opt \<leftarrow> thread_get tcb_sched_context t;
     sc_ptr \<leftarrow> assert_opt sc_opt;
     refill_ready sc_ptr
   od"

definition
  awaken :: "unit det_ext_monad"
where
  "awaken \<equiv> do
    rq \<leftarrow> gets release_queue;
    s \<leftarrow> get;
    rq1 \<leftarrow> return $ takeWhile (\<lambda>t. the (fun_of_m (refill_ready_tcb t) s)) rq;
    rq2 \<leftarrow> return $ drop (length rq1) rq;
    modify $ release_queue_update (K rq);
    mapM_x (\<lambda>t. do
      sc_opt \<leftarrow> thread_get tcb_sched_context t;
      sc_ptr \<leftarrow> assert_opt sc_opt;
      refill_unblock_check sc_ptr;
      ready \<leftarrow> refill_ready sc_ptr;
      if \<not>ready then
        tcb_release_enqueue t
      else do
        tcb_sched_action tcb_sched_append t;
        switch_if_required_to t
      od
    od) rq1
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

instantiation  det_ext_ext :: (type) state_ext_sched
begin

definition
  "schedule_det_ext_ext \<equiv> do
     reprogram \<leftarrow> gets reprogram_timer;
     when reprogram awaken;
     cur \<leftarrow> gets cur_thread;
     inq \<leftarrow> gets $ in_release_queue cur;
     cur_sched \<leftarrow> is_schedulable cur inq;
     action \<leftarrow> gets scheduler_action;
     case action of
       resume_cur_thread \<Rightarrow> do
         it \<leftarrow> gets idle_thread;
         assert (cur_sched \<or> cur = it);
         return ()
       od
     | choose_new_thread \<Rightarrow> do
         when cur_sched $ tcb_sched_action tcb_sched_enqueue cur;
         dom_time \<leftarrow> gets domain_time;
         when (dom_time = 0) next_domain;
         choose_thread;
         set_scheduler_action resume_cur_thread
       od
     | switch_thread t \<Rightarrow> do
         when cur_sched $ tcb_sched_action tcb_sched_enqueue cur;
         guarded_switch_to t;
         set_scheduler_action resume_cur_thread
       od;
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
  may omit the call to @{const switch_to_thread}.
*}
definition schedule_unit :: "(unit,unit) s_monad" where
"schedule_unit \<equiv> do
   do
     cur \<leftarrow> gets cur_thread;
     threads \<leftarrow> allActiveTCBs;
     thread \<leftarrow> select threads;
     if thread = cur then
       return () \<sqinter> switch_to_thread thread
     else
       switch_to_thread thread
   od \<sqinter>
   switch_to_idle_thread;
  sc_and_timer
od"

instance ..
end


lemmas schedule_def = schedule_det_ext_ext_def schedule_unit_def

end
