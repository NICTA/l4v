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

definition "MIN_BUDGET = 2 * kernelWCET_ticks"
definition "MIN_BUDGET_US = 2 * kernelWCET_us"


definition
  get_tcb_sc :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) s_monad" (* FIXME: RT - use this everywhere *)
where
  "get_tcb_sc tcb_ptr = do
    tcb \<leftarrow> gets_the $ get_tcb tcb_ptr;
    sc_ptr \<leftarrow> assert_opt $ tcb_sched_context tcb;
    get_sched_context sc_ptr
  od"

abbreviation
  "refill_hd sc \<equiv> hd (sc_refills sc)"

definition
  get_sc_time :: "obj_ref \<Rightarrow> time det_ext_monad"
where
  "get_sc_time tcb_ptr = do
    sc \<leftarrow> get_tcb_sc tcb_ptr;
    return $ r_time (refill_hd sc)
  od"


text \<open>Enqueue a TCB in the release queue, sorted by release time of
  the corresponding scheduling context.\<close>
definition
  tcb_release_enqueue :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "tcb_release_enqueue tcb_ptr = do
     time \<leftarrow> get_sc_time tcb_ptr;
     qs \<leftarrow> gets release_queue;
     times \<leftarrow> mapM get_sc_time qs;
     qst \<leftarrow> return $ zip qs times;
     qst' \<leftarrow> return $ filter (\<lambda>(_,t'). t' \<le> time) qst @ [(tcb_ptr,time)] @ filter (\<lambda>(_,t'). \<not>t' \<le> time) qst;
     modify (\<lambda>s. s\<lparr>release_queue := map fst qst'\<rparr>)
  od"

definition
  refills_capacity :: "time \<Rightarrow> refill list \<Rightarrow> time"
where
  "refills_capacity usage refills \<equiv>
  if r_amount (hd refills) < usage then 0 else r_amount (hd refills) - usage"

definition
  get_refills :: "obj_ref \<Rightarrow> (refill list, 'z::state_ext) s_monad"
where
  "get_refills sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    return $ sc_refills sc
  od"

definition
  refill_capacity :: "obj_ref \<Rightarrow> time \<Rightarrow> (time, 'z::state_ext) s_monad"
where
  "refill_capacity sc_ptr usage = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ refills_capacity usage refills
  od"

definition
  sufficient_refills :: "time \<Rightarrow> refill list \<Rightarrow> bool"
where
  "sufficient_refills usage refills = (MIN_BUDGET < refills_capacity usage refills)"

definition
  refill_sufficient :: "obj_ref \<Rightarrow> time \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_sufficient sc_ptr usage = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ sufficient_refills usage refills
  od"

definition
  refill_ready :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_ready sc_ptr = do
    cur_time \<leftarrow> gets cur_time;
    sc \<leftarrow> get_sched_context sc_ptr;
    sc_time \<leftarrow> return $ r_time (refill_hd sc);
    return $ sc_time \<le> cur_time + kernelWCET_ticks
  od"

definition
  refill_size :: "obj_ref \<Rightarrow> (nat, 'z::state_ext) s_monad"
where
  "refill_size sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ size refills
  od"

definition
  refill_single :: "obj_ref \<Rightarrow> (bool, 'z::state_ext) s_monad"
where
  "refill_single sc_ptr = do
    sz \<leftarrow> refill_size sc_ptr;
    return (sz = 1)
  od"

definition
  refills_sum :: "refill list \<Rightarrow> time"
where
  "refills_sum rf = \<Sum> (set (map r_amount rf))"

definition
  refill_sum :: "obj_ref \<Rightarrow> (time, 'z::state_ext) s_monad"
where
  "refill_sum sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    return $ refills_sum refills
  od"

definition
  set_refills :: "obj_ref \<Rightarrow> refill list \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_refills sc_ptr refills = do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_refills:= refills\<rparr>)
  od"

definition
  refill_pop_head :: "obj_ref \<Rightarrow> (refill, 'z::state_ext) s_monad"
where
  "refill_pop_head sc_ptr = do
    refills \<leftarrow> get_refills sc_ptr;
    assert (1 < size refills);
    set_refills sc_ptr (tl refills);
    return $ hd refills
  od"

definition
  refill_add_tail :: "obj_ref \<Rightarrow> refill \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_add_tail sc_ptr rfl = do
    assert (r_amount rfl \<noteq> 0);
    sc \<leftarrow> get_sched_context sc_ptr;
    refills \<leftarrow> return $ sc_refills sc;
    assert (size refills < sc_refill_max sc);
    set_refills sc_ptr (refills @ [rfl])
  od"

definition
  refill_new :: "obj_ref \<Rightarrow> nat \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_new sc_ptr max_refills budget period = do
    sc \<leftarrow> get_sched_context sc_ptr;
    assert (MIN_BUDGET < budget);
    cur_time \<leftarrow> gets cur_time;
    refill \<leftarrow> return \<lparr> r_time = cur_time, r_amount = budget \<rparr>;
    sc' \<leftarrow> return $ sc\<lparr> sc_period := period, sc_refills := [refill], sc_refill_max := max_refills \<rparr>;
    set_sched_context sc_ptr sc'
  od"


definition
  merge_refill :: "refill \<Rightarrow> refill \<Rightarrow> refill"
where
  "merge_refill r1 r2 = \<lparr> r_time = r_time r1, r_amount = r_amount r2 + r_amount r1 \<rparr>"

definition
  "can_merge_refill r1 r2 \<equiv> r_time r2 \<le> r_time r1 + r_amount r1"

fun
  refills_merge_prefix :: "refill list \<Rightarrow> refill list"
where
  "refills_merge_prefix [] = []"
| "refills_merge_prefix [r] = [r]"
| "refills_merge_prefix (r1 # r2 # rs) = 
     (if can_merge_refill r1 r2
      then refills_merge_prefix (merge_refill r1 r2 # rs)
      else r1 # r2 # rs)"

definition
  refill_unblock_check :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_unblock_check sc_ptr = do
    ct \<leftarrow> gets cur_time;
    refills \<leftarrow> get_refills sc_ptr;
    refills' \<leftarrow> return $ refills_merge_prefix ((hd refills)\<lparr>r_time := ct\<rparr> # tl refills);
    refills'' \<leftarrow> return (if sufficient_refills 0 refills' then refills' else
      let
        r1 = hd refills';
        r2 = hd (tl refills');
        rs = tl (tl refills')
      in \<lparr> r_time = r_time r2, r_amount = r_amount r2 + r_amount r1 \<rparr> # rs);
    set_refills sc_ptr refills''
  od"

function
  refills_budget_check :: "ticks \<Rightarrow> ticks \<Rightarrow> refill list \<Rightarrow> ticks \<times> refill list"
where
  "refills_budget_check period usage [] = (usage, [])"
| "refills_budget_check period usage (r#rs) = (if r_amount r \<le> usage \<and> 0 < r_amount r
     then refills_budget_check period (usage - r_amount r) (rs @ [r\<lparr>r_time := r_time r + period\<rparr>]) 
     else (usage, r#rs))"
  by pat_completeness auto

termination refills_budget_check
  apply (relation "measure (\<lambda>(p,u,rs). unat u)")
   apply clarsimp
  apply unat_arith
  done

definition
  refill_budget_check :: "obj_ref \<Rightarrow> ticks \<Rightarrow> (ticks, 'z::state_ext) s_monad"
where
  "refill_budget_check sc_ptr usage = do    
    sc \<leftarrow> get_sched_context sc_ptr;
    period \<leftarrow> return $ sc_period sc;
    refills \<leftarrow> return $ sc_refills sc;
    rfhd \<leftarrow> return $ hd refills;

    (usage', refills') \<leftarrow> return $ refills_budget_check period usage refills;

    refills'' \<leftarrow> return (if 0 < usage' \<and> 0 < period then
      let r1 = hd refills'; 
          r1' = r1 \<lparr>r_time := r_time r1 + usage\<rparr>;
          rs = tl refills'
      in if rs \<noteq> [] \<and> can_merge_refill r1' (hd rs) then merge_refill r1' (hd rs) # tl rs else [r1]
    else refills');

    set_refills sc_ptr refills';

    return usage'
  od"

definition
  refill_split_check :: "obj_ref \<Rightarrow> time \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_split_check sc_ptr usage = do
    ct \<leftarrow> gets cur_time;
    sc \<leftarrow> get_sched_context sc_ptr;
    refills \<leftarrow> return $ sc_refills sc;
    rfhd \<leftarrow> return $ hd refills;
    assert (0 < usage \<and> usage \<le> r_amount rfhd);
    assert (r_time rfhd \<le> ct);

    remaining \<leftarrow> return $ r_amount rfhd - usage;
    if remaining < MIN_BUDGET \<and> size refills = 1
    then
      set_refills sc_ptr [\<lparr> r_time = r_time rfhd + sc_period sc, r_amount = r_amount rfhd \<rparr>]
    else do
      if size refills = sc_refill_max sc \<or> remaining < MIN_BUDGET
      then
        let r2 = hd (tl refills); rs = tl (tl refills) in
        set_refills sc_ptr (r2 \<lparr>r_amount := r_amount r2 + remaining\<rparr> # rs)
      else
        set_refills sc_ptr (rfhd\<lparr>r_amount := remaining\<rparr> # tl refills);
      new \<leftarrow> return \<lparr> r_time = r_time rfhd + sc_period sc, r_amount = usage \<rparr>;
      refill_add_tail sc_ptr new
    od
  od"


definition
  refill_update :: "obj_ref \<Rightarrow> ticks \<Rightarrow> ticks \<Rightarrow> nat \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "refill_update sc_ptr new_period new_budget new_max_refills =
    refill_new sc_ptr new_max_refills new_budget new_period
    (* RT: may need to tweak this in the future *)
  "

definition
  postpone :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "postpone sc_ptr = do
    sc \<leftarrow> get_sched_context sc_ptr;
    tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
    do_extended_op $ tcb_sched_action tcb_sched_dequeue tcb_ptr;
    do_extended_op $ tcb_release_enqueue tcb_ptr;
    modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>)
  od"

text \<open>
  Resume a scheduling context: check if the bound TCB
  is runnable and add it to the scheduling queue if required
\<close> 
definition
  sched_context_resume :: "obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "sched_context_resume sc_ptr_opt \<equiv> case sc_ptr_opt of None \<Rightarrow> return ()
  | Some sc_ptr \<Rightarrow> do
     sc \<leftarrow> get_sched_context sc_ptr;
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     in_release_q \<leftarrow> select_ext (in_release_queue tptr) {True,False};
     sched \<leftarrow> is_schedulable tptr in_release_q;
     when sched $ do
       refill_unblock_check sc_ptr;
       ts \<leftarrow> thread_get tcb_state tptr;
       ready \<leftarrow> refill_ready sc_ptr;
       sufficient \<leftarrow> refill_sufficient sc_ptr 0;
       when (runnable ts \<and> 0 < sc_refill_max sc \<and> \<not>(ready \<and> sufficient)) $ postpone sc_ptr
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
    sched_context_resume (Some sc_ptr)
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
     tptr \<leftarrow> assert_opt $ sc_tcb sc;
     do_extended_op $ tcb_sched_action tcb_sched_dequeue tptr;
     do_extended_op $ tcb_release_remove tptr;
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
  case iv of InvokeSchedControlConfigure sc_ptr budget period mrefills \<Rightarrow> liftE $ do
    sc \<leftarrow> get_sched_context sc_ptr;
    period \<leftarrow> return (if budget = period then 0 else period);
    when (sc_tcb sc \<noteq> None) $ do
      tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
      do_extended_op $ tcb_release_remove tcb_ptr;
      st \<leftarrow> get_thread_state tcb_ptr;
      if 0 < sc_refill_max sc \<and> runnable st then do
        refill_update sc_ptr period budget mrefills;
        sched_context_resume (Some sc_ptr)
      od
      else
        refill_new sc_ptr mrefills budget period
    od
  od"


text \<open> Update time consumption of current scheduling context and current domain. \<close>
definition
  commit_time :: "(unit, 'z::state_ext) s_monad"
where
  "commit_time = do
    consumed \<leftarrow> gets consumed_time;
    ct \<leftarrow> gets cur_thread;
    it \<leftarrow> gets idle_thread;
    when (0 < consumed \<and> ct \<noteq> it) $ do
      csc \<leftarrow> gets_the cur_sc;
      refill_split_check csc consumed
    od;
    do_extended_op $ commit_domain_time;
    modify (\<lambda>s. s\<lparr>consumed_time := 0\<rparr> )
  od"


section "Global time"

definition
  rollback_time :: "(unit, 'z::state_ext) s_monad"
where
  "rollback_time = do
    consumed \<leftarrow> gets consumed_time;
    modify (\<lambda>s. s\<lparr>cur_time := cur_time s - consumed \<rparr>);
    modify (\<lambda>s. s\<lparr>consumed_time := 0\<rparr> )
  od"


text \<open>Update current and consumed time.\<close>
definition
  update_time_stamp :: "(unit, 'z::state_ext) s_monad"
where
  "update_time_stamp = do
    prev_time \<leftarrow> gets cur_time;
    cur_time' \<leftarrow> do_machine_op getCurrentTime;
    modify (\<lambda>s. s\<lparr> cur_time := cur_time' \<rparr>);
    modify (\<lambda>s. s\<lparr> consumed_time := cur_time' - prev_time \<rparr>)
  od"

end
