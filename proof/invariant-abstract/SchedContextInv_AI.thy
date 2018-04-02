(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory SchedContextInv_AI
imports "./$L4V_ARCH/ArchIpc_AI"
begin

text {* valid invocation definitions *}

primrec
  valid_sched_context_inv :: "sched_context_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_context_inv (InvokeSchedContextConsumed scptr args)
     = (sc_at scptr and ex_nonz_cap_to scptr)"
  | "valid_sched_context_inv (InvokeSchedContextBind scptr cap)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow> bound_sc_tcb_at (op = None) t
                                      and ex_nonz_cap_to t and sc_tcb_sc_at (op = None) scptr
             | NotificationCap n _ _ \<Rightarrow>
                   obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_sc ntfn = None) n
                   and ex_nonz_cap_to n  and sc_ntfn_sc_at (op = None) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbindObject scptr cap)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr and valid_cap cap and
          (case cap of ThreadCap t \<Rightarrow>
                   ex_nonz_cap_to t and sc_tcb_sc_at (\<lambda>tcb. tcb = (Some t)) scptr
             | NotificationCap n _ _ \<Rightarrow>
                   ex_nonz_cap_to n and sc_ntfn_sc_at (\<lambda>ntfn. ntfn = (Some n)) scptr
             | _ \<Rightarrow> \<lambda>_. False))"
  | "valid_sched_context_inv (InvokeSchedContextUnbind scptr)
     = (sc_at scptr and ex_nonz_cap_to scptr)"
  | "valid_sched_context_inv (InvokeSchedContextYieldTo scptr args)
     = ((*sc_at scptr and *)ex_nonz_cap_to scptr(* and (\<lambda>s. st_tcb_at (op = Restart) (cur_thread s) s)*)
          and (\<lambda>s. ex_nonz_cap_to (cur_thread s) s)
          and sc_yf_sc_at (op = None) scptr and (\<lambda>s. bound_yt_tcb_at (op = None) (cur_thread s) s)
          and (\<lambda>s. sc_tcb_sc_at (\<lambda>sctcb.\<exists>t. sctcb = Some t \<and> t \<noteq> cur_thread s
                 (*  \<and> (mcpriority_tcb_at (\<lambda>mcp. (tcb_priority (the (get_etcb t s))) \<le> mcp)
                                                                      (cur_thread s) s)*)) scptr s))"


definition
  valid_extra_refills :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "valid_extra_refills mrefills n \<equiv>
    mrefills \<le> (n - core_sched_context_bytes) div refill_size_bytes"

primrec
  valid_sched_control_inv :: "sched_control_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
    "valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)
     = (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> valid_extra_refills mrefills n) scptr
        and ex_nonz_cap_to scptr and K (MIN_REFILLS \<le> mrefills) (* mrefills = MIN_REFILLS + extra_refills *)
        and K (budget \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_BUDGET)
        and K (period \<le> us_to_ticks maxTimer_us \<and> budget \<ge> MIN_BUDGET)
        and K (budget \<le> period))"


text {* refill invariant proofs *}  (* FIXME move? Sporadic_AI? *)

definition valid_refill_amount :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refill_amount scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> refills_sum (sc_refills sc) = budget) scptr)"

definition valid_refill_length :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refill_length scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS))) scptr)"

definition valid_refills :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refills scptr budget =
     (obj_at (\<lambda>ko. \<exists>sc n. ko= SchedContext sc n
      \<and> refills_sum (sc_refills sc) = budget
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS))) scptr)"

lemma valid_refills_def2:
  "valid_refills = (\<lambda>p b. valid_refill_amount p b and valid_refill_length p b)"
  by (fastforce simp: valid_refills_def valid_refill_amount_def valid_refill_length_def obj_at_def)

definition sc_valid_refills :: "sched_context \<Rightarrow> time \<Rightarrow> bool"
where
  "sc_valid_refills sc budget =
      (refills_sum (sc_refills sc) = budget
      \<and> 1 \<le> length (sc_refills sc)
      \<and> MIN_REFILLS \<le> sc_refill_max sc
      \<and> length (sc_refills sc) \<le> sc_refill_max sc
      \<and> (sc_period sc = 0 \<longrightarrow> (sc_refill_max sc = MIN_REFILLS
                               \<and> length (sc_refills sc) = MIN_REFILLS)))"

lemma valid_refills_consumed_time_update[iff]:
  "valid_refills p b (consumed_time_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_scheduler_action_update[iff]:
  "valid_refills p b (scheduler_action_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_ready_queues_update[iff]:
  "valid_refills p b (ready_queues_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_release_queue_update[iff]:
  "valid_refills p b (release_queue_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def)

lemma valid_refills_kheap_tcb_update[iff]:
  "tcb_at t s \<Longrightarrow> valid_refills p b (s\<lparr>kheap := kheap s(t \<mapsto> TCB tcb)\<rparr>) = valid_refills p b s"
  by (clarsimp simp: valid_refills_def obj_at_def is_tcb)

crunch valid_refills[wp]: tcb_sched_action,set_scheduler_action,refill_capacity,refill_sufficient
   "valid_refills scp budget"
crunch valid_refills[wp]: tcb_release_enqueue,tcb_release_remove,refill_ready "valid_refills scp budget"
  (wp: crunch_wps)

crunch valid_refills[wp]: reschedule_required,
possible_switch_to "valid_refills scp budget"
  (wp: dxo_wp_weak hoare_vcg_if_lift2 crunch_wps)

lemma valid_refills_exst [iff]:
  "valid_refills p b (trans_state f s) = valid_refills p b s"
  by (simp add: valid_refills_def valid_state_def)

lemma valid_refills_reprogram_timer_update [iff]:
  "valid_refills p b (reprogram_timer_update f s) = valid_refills p b s"
  by (simp add: valid_refills_def valid_state_def)

lemma sched_context_resume_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> sched_context_resume p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: sched_context_resume_def wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunch valid_refills[wp]: sort_queue "valid_refills scp budget"  (wp: mapM_wp')

lemma set_sched_context_valid_refills_no_budget_update:
  "\<lbrace>valid_refills scptr budget
     and K (scptr=p \<longrightarrow> sc_valid_refills newsc budget)\<rbrace>
     set_sched_context p newsc
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: valid_refills_def set_sched_context_def obj_at_def sc_valid_refills_def
          wp: set_object_wp get_object_wp)

lemma set_sched_context_valid_refills:
  "\<lbrace>valid_refills scptr budget
     and K (1 \<le> length (sc_refills newsc)\<and>MIN_REFILLS \<le> sc_refill_max newsc
         \<and> length (sc_refills newsc) \<le> sc_refill_max newsc
         \<and> (sc_period newsc = 0 \<longrightarrow> (sc_refill_max newsc = MIN_REFILLS
                               \<and> length (sc_refills newsc) = MIN_REFILLS)))\<rbrace>
     set_sched_context p newsc
      \<lbrace>\<lambda>_. valid_refills scptr (if p = scptr then refills_sum (sc_refills newsc) else budget)\<rbrace>"
  apply (wpsimp simp: valid_refills_def set_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp split_del: if_split)
  by clarsimp

lemma set_sched_context_valid_refills':
  "\<lbrace>K (1 \<le> length (sc_refills newsc) \<and> MIN_REFILLS \<le> sc_refill_max newsc
          \<and> length (sc_refills newsc) \<le> sc_refill_max newsc
          \<and> (sc_period newsc = 0 \<longrightarrow> (sc_refill_max newsc = MIN_REFILLS
                               \<and> length (sc_refills newsc) = MIN_REFILLS)))\<rbrace>
   set_sched_context p newsc  \<lbrace>\<lambda>_. valid_refills p (refills_sum (sc_refills newsc))\<rbrace>"
  by (wpsimp simp: valid_refills_def set_sched_context_def obj_at_def
            wp: set_object_wp get_object_wp)

lemma update_sched_context_valid_refills_no_budget_update:
  "\<lbrace>valid_refills scptr budget and K (\<forall>sc. sc_valid_refills sc budget \<longrightarrow> sc_valid_refills (f sc) budget)\<rbrace>
     update_sched_context p f
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp)
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)

lemma set_thread_state_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> set_thread_state tp st \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp wp: sts_obj_at_impossible simp: valid_refills_def)

lemma refill_add_tail_valid_refills:
  "\<lbrace>valid_refills scptr budget\<rbrace>
     refill_add_tail p new
      \<lbrace>\<lambda>_. valid_refills scptr (budget + (if scptr = p then r_amount new else 0))\<rbrace>"
  apply (wpsimp wp: get_refills_wp get_sched_context_wp set_object_wp get_object_wp
           simp: refill_add_tail_def set_refills_def update_sched_context_def split_del: if_split)
  by (clarsimp simp: valid_refills_def obj_at_def refills_sum_def)

lemma maybe_add_empty_tail_valid_refills:
  "\<lbrace>valid_refills scptr budget\<rbrace> maybe_add_empty_tail p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp wp: get_refills_wp get_sched_context_wp set_object_wp get_object_wp
           simp: maybe_add_empty_tail_def refill_add_tail_def is_round_robin_def
                 set_refills_def update_sched_context_def)
  by (clarsimp simp: valid_refills_def obj_at_def refills_sum_def)

lemma refill_new_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget and K (MIN_REFILLS \<le> max_refills \<and> (period = 0 \<longrightarrow> max_refills = MIN_REFILLS))\<rbrace>
    refill_new p max_refills budget period \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: refill_new_def update_sched_context_def maybe_add_empty_tail_def
           refill_add_tail_def set_refills_def is_round_robin_def
            wp:  set_object_wp get_object_wp get_sched_context_wp)
  by (clarsimp simp: valid_refills_def refills_sum_def obj_at_def MIN_REFILLS_def)

lemma refill_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr new_budget and
    K (MIN_REFILLS \<le> new_max_refills \<and> (new_period = 0 \<longrightarrow> new_max_refills = MIN_REFILLS))\<rbrace>
     refill_update p new_period new_budget new_max_refills
      \<lbrace>\<lambda>_. valid_refills scptr new_budget\<rbrace>"
  apply (clarsimp simp: refill_update_def)
  apply (rule hoare_assume_pre)
  apply (wpsimp simp: set_refills_def get_refills_def set_object_def is_round_robin_def
                      set_sched_context_def maybe_add_empty_tail_def refill_add_tail_def
                      update_sched_context_def
                split_del: if_split
                wp: get_object_wp get_sched_context_wp hoare_vcg_if_lift2)
  apply clarsimp
  apply (intro conjI impI; clarsimp simp: valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
  done

lemma sum_list_but_last[iff]:
  "lista \<noteq> [] \<Longrightarrow> sum_list (map r_amount (butlast lista)) + r_amount (last lista) =
            sum_list (map r_amount lista)"
  apply (subgoal_tac "sum_list (map r_amount (butlast lista)) + r_amount (last lista)
           = sum_list (map r_amount ((butlast lista) @ [last lista]))")
   apply (drule trans)
    prefer 2
    apply simp
   apply (subst append_butlast_last_id)
    apply blast+
  apply (clarsimp simp del:append_butlast_last_id)+
  done

lemma schedule_used_non_nil:
  "Suc 0 \<le> length (schedule_used x new)" 
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length':
  "length (schedule_used x new) = length x \<or> length (schedule_used x new) = length x + 1"
  by (induct x; clarsimp simp: Let_def)

lemma schedule_used_length:
  "length (schedule_used x new) =
   (if ((r_amount new < MIN_BUDGET \<and> 2 \<le> length x) \<or> (x \<noteq> [] \<and> r_time new \<le> r_time (last x)))
    then length x else length x + 1)"
  by (induct x; clarsimp simp: Let_def length_greater_0_conv[symmetric] simp del: length_greater_0_conv)

lemma schedule_used_sum [simp]:
  "refills_sum (schedule_used refills new) = refills_sum (refills @ [new])"
  apply (induct refills arbitrary: new, simp)
  apply (clarsimp simp: refills_sum_def Let_def)
  done

lemma refills_budget_check_pos:
  "\<lbrakk>refills_budget_check period usage rfls = (t, ls); Suc 0 \<le> length rfls\<rbrakk>
    \<Longrightarrow> Suc 0 \<le> length ls "
  apply (induct rfls arbitrary: t ls rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (clarsimp simp add: schedule_used_non_nil)
  done

lemma refills_budget_check_length[intro]:
  "Suc 0 \<le> length rfls \<Longrightarrow> Suc 0 \<le> length (snd (refills_budget_check period usage rfls))"
  apply (induct rfls arbitrary:  rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (clarsimp simp add: schedule_used_non_nil)
  done

lemma refills_budget_check_length_max[intro]:
  "length rfls \<le> L \<Longrightarrow> length (snd (refills_budget_check period usage rfls)) \<le> L"
  apply (induct rfls arbitrary: L rule: refills_budget_check.induct)
   apply simp
  apply simp
  apply (clarsimp simp: split: if_split_asm)
  apply (drule_tac x=L in meta_spec)
  apply (drule meta_mp)
  apply (clarsimp simp add: schedule_used_non_nil schedule_used_length)
  apply simp
  done

lemma refills_sum_cons[simp]: "refills_sum (a#rs) =  r_amount a + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_append[simp]: "refills_sum (rs1 @ rs) =  refills_sum rs1 + refills_sum rs"
  by (clarsimp simp: refills_sum_def)

lemma refills_sum_nil[simp]: "refills_sum [] = 0" by (clarsimp simp: refills_sum_def)

lemma refills_budget_check_sum [simp]:
  "refills_sum (snd (refills_budget_check period usage rfls)) = refills_sum (rfls)"
  apply (induct usage arbitrary: rfls rule: measure_induct[where f=id])
  apply simp
  apply (induct_tac rfls, simp)
  apply (clarsimp split: if_split_asm)
  apply (drule_tac x="x - r_amount a" in spec)
  apply (subgoal_tac "x - r_amount a < x")
   apply (clarsimp)
  by (simp add: word_diff_less)

lemma valid_refills_sc_update:
  "(valid_refills p b (s\<lparr>kheap := kheap s(p \<mapsto> SchedContext sc n)\<rparr>))
       = (sc_valid_refills sc b)"
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)


definition
  sc_at_period :: "(time \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "sc_at_period P  = obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> P (sc_period sc))"

lemma refill_split_check_valid_refills[wp]: (* applicable only when sc is not round_robin *)
  "\<lbrace>valid_refills scptr budget and sc_at_period (\<lambda>p. p \<noteq> 0) p\<rbrace>
      refill_split_check p consumed \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (unfold refill_split_check_def)
  apply (simp add: Let_def set_refills_def set_sched_context_def sc_at_period_def obj_at_def
      del: schedule_used.simps split del: if_split)
  apply (rule hoare_seq_ext[OF _ gets_wp])
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (clarsimp split del: if_split simp del: schedule_used.simps)
  apply (case_tac "length (sc_refills x) = sc_refill_max x \<or>
             r_amount (refill_hd x) - consumed < MIN_BUDGET")
   apply (case_tac "length (sc_refills x) = Suc 0")
    apply (clarsimp split del: if_split)
    apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
      hoare_vcg_if_lift2 hoare_drop_imp
      simp: update_sched_context_def simp_del: schedule_used.simps  split_del: if_split)
    apply (case_tac "sc_refills x"; clarsimp simp: valid_refills_def obj_at_def refills_sum_def)

   apply (clarsimp split del: if_split simp del: schedule_used.simps)
   apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
      hoare_vcg_if_lift2 hoare_drop_imp
      simp: update_sched_context_def simp_del: schedule_used.simps  split_del: if_split)
   apply (case_tac "p=scptr")
    apply (clarsimp simp: valid_refills_def obj_at_def schedule_used_length MIN_REFILLS_def
      simp del: schedule_used.simps split del: if_split)
    apply (case_tac "sc_refills x", simp)
    apply (case_tac "list"; clarsimp simp: valid_refills_def obj_at_def refills_sum_def)
   apply (clarsimp simp: valid_refills_def obj_at_def)
  apply (clarsimp split del: if_split simp del: schedule_used.simps)
  apply (wpsimp wp: get_refills_wp set_object_wp get_object_wp get_sched_context_wp
      hoare_vcg_if_lift2 hoare_drop_imp
      simp: update_sched_context_def simp_del: schedule_used.simps  split_del: if_split)
  apply (case_tac "p=scptr")
   apply (clarsimp simp: valid_refills_def obj_at_def schedule_used_length MIN_REFILLS_def
      simp del: schedule_used.simps split del: if_split)
   apply (case_tac "sc_refills x", simp)
   apply (case_tac "list"; clarsimp simp: valid_refills_def obj_at_def refills_sum_def)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  done

lemma min_budget_merge_helper:
   "refills_sum (min_budget_merge b (r0#r1#rs)) = refills_sum (r0#r1#rs)"
  apply (induction rs arbitrary: r0 r1 b, clarsimp simp: refills_sum_def)
  apply (clarsimp)
  apply (drule_tac x="r1\<lparr>r_amount := r_amount r1 + r_amount r0\<rparr>" in meta_spec)
  apply (drule_tac x=a in meta_spec)
  apply (clarsimp simp: refills_sum_def)
 done

lemma min_budget_merge_refills_sum[iff]:
  "refills_sum (min_budget_merge b refills) = refills_sum refills"
  apply (cases refills, simp)
  apply (case_tac list, simp)
  by (simp only: min_budget_merge_helper)

lemma min_budget_merge_length_helper:
  "1 \<le> length (min_budget_merge b (r0#r1#rs)) \<and> length (min_budget_merge b (r0#r1#rs)) \<le> length (r0#r1#rs)"
  apply (induction rs arbitrary: r0 r1 b, simp)
  apply (clarsimp split del: if_split)
  apply (drule_tac x="r1\<lparr>r_amount := r_amount r1 + r_amount r0\<rparr>" in meta_spec)
  apply (drule_tac x=a in meta_spec)
  by clarsimp

lemma min_budget_merge_length:
  "1 \<le> length ls \<Longrightarrow> 1 \<le> length (min_budget_merge b ls) \<and> length (min_budget_merge b ls) \<le> length ls"
  apply (cases ls, simp)
  apply (case_tac list, simp)
  by (simp only: min_budget_merge_length_helper)


lemma set_min_budget_merge_valid_refills:
  "\<lbrace>valid_refills scptr budget
    and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n \<and> sc_period sc \<noteq> 0) p\<rbrace>
    set_refills p (min_budget_merge full (sc_refills sc)) \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
apply (unfold set_refills_def)
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  apply (drule min_budget_merge_length[of "sc_refills sc" full, simplified])
  apply auto
  done

crunch obj_at[wp]: refill_full "obj_at P p"

lemma refill_full_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> refill_full p \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  by (wpsimp simp: refill_full_def)
lemma refills_budget_check_valid_refills:
  "\<lbrace>valid_refills scptr budget
    and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n \<and> sc_period sc \<noteq> 0) p\<rbrace>
    set_refills p (snd (refills_budget_check (sc_period sc) usage (sc_refills sc)))
   \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def)
  apply (drule refills_budget_check_length[where rfls="sc_refills sc", simplified])
  apply auto
  done

lemma update_sc_consumed_valid_refills[wp]:
  "\<lbrace>valid_refills p budget and sc_at ptr\<rbrace>
   update_sched_context ptr (\<lambda>sc. sc_consumed_update f sc)
      \<lbrace>\<lambda>_. valid_refills p budget\<rbrace>"
  by (wpsimp simp: valid_refills_def update_sched_context_def obj_at_def
            wp: set_object_wp get_object_wp)

lemma update_min_budget_merge_valid_refills:
  "\<lbrace>valid_refills scptr budget and sc_at_period (\<lambda>p. p \<noteq> 0) p\<rbrace>
    update_sched_context p (sc_refills_update (min_budget_merge full))
    \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
                wp: get_object_wp get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_at_period_def)
  apply (drule_tac ls="sc_refills x" in min_budget_merge_length[of _ full, simplified])
  apply auto
  done


lemma helper0:
  "\<lbrace>valid_refills scptr budget
     and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s) \<and> 0 < sc_period sc) \<rbrace>
      set_refills p
              (if 0 < fst (refills_budget_check (sc_period sc) usage (sc_refills sc))
               then let r1 = hd (snd (refills_budget_check (sc_period sc) usage
                                       (sc_refills sc)));
                        r1' = r1\<lparr>r_time := r_time r1 + usage\<rparr>;
                        rs = tl (snd (refills_budget_check (sc_period sc) usage
                                       (sc_refills sc)))
                    in if rs \<noteq> [] \<and> can_merge_refill r1' (hd rs)
                       then merge_refill r1' (hd rs) # tl rs else r1' # rs
               else snd (refills_budget_check (sc_period sc) usage (sc_refills sc)))
                     \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
      wp: get_object_wp split_del: if_split)
  apply (clarsimp simp: obj_at_def valid_refills_def word_gt_0 split del: if_split)
  apply (case_tac "scptr=p"; simp split del: if_split)
  apply (frule_tac period="(sc_period sca)" and usage=usage in refills_budget_check_length)
  apply (frule_tac period="(sc_period sca)" and usage=usage in refills_budget_check_length_max)
  apply (clarsimp simp: split del: if_split)
  apply (clarsimp simp: can_merge_refill_def merge_refill_def Let_def MIN_REFILLS_def
          split del: if_split cong: if_cong)
  apply (case_tac "snd (refills_budget_check (sc_period sc) usage (sc_refills sc))"; simp split del: if_split)
  apply (case_tac list; simp split del: if_split)
   apply (subst refills_budget_check_sum[of "(sc_period sc)" usage "(sc_refills sc)", symmetric])
   apply (simp split del: if_split)
   apply (clarsimp simp: split del: if_split)
   apply (intro conjI)
     defer
     apply (clarsimp+)[2]
   apply (subst refills_budget_check_sum[of "(sc_period sc)" usage "(sc_refills sc)", symmetric], simp split del: if_split)
   apply clarsimp
  apply (clarsimp simp: refill_sum_def)
  done

crunch sc_at_period[wp]: refill_full "sc_at_period P p"

lemma set_refills_sc_at_period[wp]:
  "\<lbrace>sc_at_period P p\<rbrace> set_refills sc_ptr refills \<lbrace>\<lambda>_. sc_at_period P p\<rbrace>"
  apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def
             wp: get_object_wp)
  by (clarsimp simp: sc_at_period_def obj_at_def)

lemma refill_split_check_sc_at_period[wp]:
  "\<lbrace>sc_at_period P p\<rbrace> refill_split_check sc_ptr usage \<lbrace>\<lambda>_. sc_at_period P p\<rbrace>"
  apply (clarsimp simp: refill_split_check_def)
  apply (wpsimp simp: Let_def split_del: if_split wp: get_sched_context_wp)
  done

lemma refill_budget_check_valid_refills[wp]:
   "\<lbrace>valid_refills scptr budget and sc_at_period (\<lambda>p. p \<noteq> 0) p\<rbrace>
      refill_budget_check p usage capacity \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (case_tac "capacity = 0"; simp add: split_def split del: if_split)
   apply (wpsimp wp: update_min_budget_merge_valid_refills helper0 split_del: if_split)
  apply (wpsimp wp: update_min_budget_merge_valid_refills)
   apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def wp: get_object_wp)
  apply (fastforce simp: valid_refills_def obj_at_def sc_at_period_def)
  done

lemma valid_refills_sc_consumed_update[iff]:
    "valid_refills p b (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext (sc\<lparr>sc_consumed:=x\<rparr>) n)\<rparr>)
         = valid_refills p b (s\<lparr>kheap := kheap s(p' \<mapsto> SchedContext sc n)\<rparr>)"
  by (clarsimp simp: valid_refills_def obj_at_def)

lemma commit_time_valid_refills[wp]:
  "\<lbrace>\<lambda>s. valid_refills ptr budget s\<rbrace> commit_time \<lbrace>\<lambda>_ s. valid_refills ptr budget s\<rbrace>"
  apply (clarsimp simp: commit_time_def)
  apply (wpsimp simp: set_object_def sc_valid_refills_def
      wp: get_object_wp update_sc_consumed_valid_refills update_sched_context_valid_refills_no_budget_update
      simp_del: fun_upd_apply)
       apply (wpsimp simp: set_refills_def set_object_def update_sched_context_def
      wp: get_object_wp get_sched_context_wp )
      apply (wpsimp simp: sc_valid_refills_def wp: refill_split_check_valid_refills get_sched_context_wp)
     apply (wpsimp wp: get_sched_context_wp)+
  apply (rule conjI; clarsimp split del: if_split)
   apply (rule conjI; clarsimp split del: if_split)
    apply (clarsimp simp: valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
    apply (case_tac "sc_refills sc", simp)
    apply (case_tac list; simp)
   apply (clarsimp simp: sc_valid_refills_def valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
   apply (clarsimp simp: sc_at_period_def obj_at_def)
  apply (clarsimp simp: sc_valid_refills_def valid_refills_def obj_at_def refills_sum_def MIN_REFILLS_def)
  done

lemmas valid_refills_kheap_tcb_update'[iff] = valid_refills_kheap_tcb_update[simplified fun_upd_def obj_at_def is_tcb]

lemma thread_set_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: thread_set_def set_object_def simp_del: fun_upd_apply)
  apply (clarsimp simp: dest!:get_tcb_SomeD)
  done

lemma set_simple_ko_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> set_simple_ko C ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def set_object_def partial_inv_def a_type_def
         wp: get_object_wp simp_del: fun_upd_apply split: kernel_object.splits)
  apply (intro conjI impI; clarsimp simp: valid_refills_def obj_at_def)
  done

lemma sc_replies_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_sc_obj_ref sc_replies_update ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma sc_tcb_update_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_sc_obj_ref sc_tcb_update ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_sc_obj_ref_def set_object_def
         wp: get_object_wp update_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma set_tcb_obj_ref_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      set_tcb_obj_ref f ptr new \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def
         wp: get_object_wp set_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def dest!: get_tcb_SomeD)
  done

crunch valid_refills[wp]: update_sk_obj_ref "valid_refills scp budget"
 (wp: set_sched_context_valid_refills_no_budget_update simp: )

lemma sched_context_donate_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      sched_context_donate ptr callee \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: sched_context_donate_def set_object_def get_sc_obj_ref_def
         wp: get_object_wp set_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  done

lemma reply_push_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: reply_push_def set_object_def partial_inv_def a_type_def
              unbind_reply_in_ts_def no_reply_in_ts_def
         wp: get_object_wp set_sched_context_valid_refills_no_budget_update get_sched_context_wp
             hoare_drop_imp hoare_vcg_if_lift2 hoare_vcg_all_lift
         simp_del: fun_upd_apply split: kernel_object.splits)
  done

crunch valid_refills[wp]: reply_unlink_tcb "valid_refills scp budget"
 (wp: set_sched_context_valid_refills_no_budget_update gts_inv hoare_drop_imps)

locale SchedContextInv_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes some_t :: "'t itself"
  assumes make_arch_fault_msg_valid_refills[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes lookup_ipc_buffer_valid_refills[wp]:
    "\<And>t b scptr budget.
      \<lbrace>valid_refills scptr budget :: 'state_ext state \<Rightarrow> bool\<rbrace>
        lookup_ipc_buffer b t
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"

lemma as_user_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
      as_user t f \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: as_user_def split_def)
  apply (wpsimp wp: select_f_wp set_object_wp)
  by (clarsimp dest!: get_tcb_SomeD simp: valid_refills_def obj_at_def)

crunch valid_refills[wp]: set_message_info "valid_refills scp budget"
crunch valid_refills[wp]: set_cdt,set_original,set_extra_badge "valid_refills scp budget"
  (simp: valid_refills_def)


lemma set_cap_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> set_cap c p \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wpsimp simp: set_object_def wp: get_object_wp)
  apply (fastforce simp: valid_refills_def obj_at_def)
  done

crunch valid_refills[wp]: cap_insert "valid_refills scp budget"
  (wp: hoare_drop_imps)

lemma dmo_storeWord_valid_refills[wp]:
  "\<lbrace>valid_refills scp budget\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>_. valid_refills scp budget\<rbrace>"
  by (simp add: do_machine_op_def valid_refills_def |  wp | wpc)+

lemma sched_context_update_consumed_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> sched_context_update_consumed scptr \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: sched_context_update_consumed_def)
  apply (wpsimp simp: set_object_def
      wp: get_object_wp set_sched_context_valid_refills_no_budget_update get_sched_context_wp)
  apply (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)
  done

lemma set_mrs_valid_refills [wp]:
 "\<lbrace>valid_refills scp budget\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  apply (simp add: set_mrs_def split_def)
  apply (wpsimp simp: set_object_def zipWithM_x_mapM_x wp: get_object_wp mapM_x_wp' split_del: if_split)
  apply (clarsimp simp: valid_refills_def obj_at_def get_tcb_SomeD)
  done

crunch valid_refills[wp]: copy_mrs "valid_refills scp budget"
  (wp: mapM_wp')

lemma transfer_caps_loop_valid_refills[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_refills scp budget\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_refills scp budget\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_refills)


context SchedContextInv_AI begin

crunch valid_refills[wp]: do_ipc_transfer "valid_refills scp budget :: 'state_ext state \<Rightarrow> bool"

end

locale SchedContextInv_AI2 = SchedContextInv_AI state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself" and some_t :: "'t itself"+
  assumes  send_ipc_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> send_ipc block call badge can_grant can_donate thread epptr
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"

context SchedContextInv_AI2 begin

crunch valid_refills[wp]: handle_timeout "valid_refills scp budget"

lemma end_timeslice_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> end_timeslice canTimeout \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: end_timeslice_def)
  by (wpsimp simp: end_timeslice_def wp: hoare_drop_imps split_del: if_split)

lemma update_sched_context_valid_refills_sc_consumed_update:
  "\<lbrace>valid_refills scptr budget\<rbrace>
     update_sched_context p (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>) 
      \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (wpsimp simp: update_sched_context_def obj_at_def
          wp: set_object_wp get_object_wp)
  by (clarsimp simp: valid_refills_def obj_at_def sc_valid_refills_def)

lemma charge_budget_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace>
     charge_budget capacity consumed canTimeout \<lbrace>\<lambda>_ s. valid_refills scptr budget s\<rbrace>"
  apply (clarsimp simp: charge_budget_def is_round_robin_def)
  apply (wpsimp wp: get_object_wp update_sched_context_valid_refills_sc_consumed_update
      simp: Let_def is_round_robin_def refill_full_def)
       apply (wpsimp simp: set_refills_def update_sched_context_def set_object_def wp: get_object_wp)
      apply clarsimp
      apply (wpsimp wp: get_refills_wp refill_budget_check_valid_refills get_sched_context_wp)+
  apply (clarsimp simp: obj_at_def MIN_REFILLS_def sc_at_period_def valid_refills_def)
  apply (case_tac "sc_refills sc"; simp)
  apply (case_tac list; simp)
  done

lemma check_budget_valid_refills[wp]:
  "\<lbrace>valid_refills scptr budget\<rbrace> check_budget \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: check_budget_def)
  by (wpsimp simp: is_round_robin_def refill_full_def refill_size_def refill_capacity_def
    wp: get_sched_context_wp get_refills_wp charge_budget_valid_refills)

lemma
  "\<lbrace>valid_refills scptr budget and
   valid_sched_control_inv (InvokeSchedControlConfigure scptr budget period mrefills badge)\<rbrace>
   invoke_sched_control_configure (InvokeSchedControlConfigure scptr budget period mrefills badge)
   \<lbrace>\<lambda>_. valid_refills scptr budget\<rbrace>"
  apply (clarsimp simp: invoke_sched_control_configure_def)
  apply (rule conjI; wpsimp simp: invoke_sched_control_configure_def split_def cong: if_cong conj_cong
             wp: hoare_vcg_if_lift2 get_sched_context_wp commit_time_valid_refills hoare_gets_sp
                 hoare_drop_imp set_sched_context_valid_refills_no_budget_update hoare_when_wp
            split_del: if_split)
  by (clarsimp simp: valid_refills_def sc_valid_refills_def obj_at_def MIN_REFILLS_def refills_sum_def)+

end

text {* invocation related lemmas *}

lemma sched_context_bind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_bind_tcb sc tcb \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_bind_tcb_def)

lemma sched_context_yield_to_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
      sched_context_yield_to sc_ptr args \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_yield_to_def wp: hoare_drop_imp hoare_vcg_if_lift2)

lemma invoke_sched_context_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_context i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i;
      wpsimp wp: dxo_wp_weak mapM_x_wp get_sched_context_wp
       simp: invoke_sched_context_def sched_context_bind_ntfn_def)

crunch typ_at[wp]: charge_budget "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

lemma check_budget_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> check_budget \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: check_budget_def split_del: if_split
            wp: hoare_vcg_if_lift2 hoare_drop_imp)

crunch typ_at[wp]: commit_time "\<lambda>s::det_ext state. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

crunch typ_at[wp]: tcb_release_remove "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imp simp: Let_def)

lemma invoke_sched_control_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     invoke_sched_control_configure i
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (cases i; wpsimp simp: invoke_sched_control_configure_def split_del: if_splits
                  wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma invoke_sched_context_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_context_typ_at [where P=id, simplified])

lemma invoke_sched_control_tcb[wp]:
  "\<lbrace>tcb_at tptr\<rbrace> invoke_sched_control_configure i \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  by (simp add: tcb_at_typ invoke_sched_control_typ_at [where P=id, simplified])

lemma invoke_sched_context_invs[wp]:
  "\<lbrace>invs and valid_sched_context_inv i\<rbrace> invoke_sched_context i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i;
      wpsimp simp: invoke_sched_context_def set_consumed_def valid_sched_context_inv_def)
   apply (clarsimp simp: obj_at_def sc_tcb_sc_at_def sc_ntfn_sc_at_def is_sc_obj_def is_tcb
      valid_cap_def idle_no_ex_cap split: cap.split_asm)+
   apply (frule invs_valid_global_refs)
   apply (frule invs_valid_objs, clarsimp simp: idle_no_ex_cap)
  apply (frule invs_valid_global_refs)
  apply (frule invs_valid_objs, clarsimp simp: idle_no_ex_cap)
  done

lemma update_sc_badge_invs:
  "\<lbrace>invs and (\<lambda>s. (\<exists>n. ko_at (SchedContext sc n) p s))\<rbrace>
      set_sched_context p (sc\<lparr>sc_badge := i \<rparr>) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def obj_at_def
                simp_del: fun_upd_apply)
  apply safe
    apply (fastforce simp: valid_objs_def valid_obj_def)
   apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def live_def)
  by (clarsimp simp: state_refs_of_def refs_of_def fun_upd_idem)

(* FIXME copied from Syscall_AI *)
lemmas si_invs = si_invs'[where Q=\<top>,OF hoare_TrueI hoare_TrueI hoare_TrueI hoare_TrueI,simplified]
thm si_invs

lemma send_ipc_invs_for_timeout:
  "\<lbrace>invs and st_tcb_at active tptr and ex_nonz_cap_to tptr
   and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)
   and K (is_ep_cap cap)\<rbrace>
      send_ipc True False (cap_ep_badge cap) True
                 canDonate tptr (cap_ep_ptr cap) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp wp: si_invs simp: obj_at_def pred_tcb_at_def)
  apply (clarsimp simp: ex_nonz_cap_to_def pred_tcb_at_def obj_at_def)
  apply (simp (no_asm) add: cte_wp_at_cases2)
  apply (rule_tac x="tptr" in exI)
  apply (rule_tac x="tcb_cnode_index 4" in exI)
  apply (clarsimp simp: tcb_cnode_map_def)
  apply (clarsimp simp: caps_of_state_tcb_index_trans[OF get_tcb_rev])
  apply (cases cap; simp)
  apply (clarsimp simp: tcb_cnode_map_def cte_wp_at_caps_of_state)
 done

(* FIXME copied from Syscall_AI *)
lemma thread_set_cap_to:
  "(\<And>tcb. \<forall>(getF, v)\<in>ran tcb_cap_cases. getF (f tcb) = getF tcb)
  \<Longrightarrow> \<lbrace>ex_nonz_cap_to p\<rbrace> thread_set f tptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  apply (clarsimp simp add: ex_nonz_cap_to_def)
  apply (wpsimp wp: hoare_ex_wp thread_set_cte_wp_at_trivial)
  done

lemma thread_set_timeout_fault_valid_mdb[wp]:
  "\<lbrace>valid_mdb\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some (Timeout badge))) t \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (rule valid_mdb_lift)
    apply wp
    apply clarsimp
    apply (subst caps_of_state_after_update)
     apply (clarsimp simp: ran_tcb_cap_cases)
    apply simp
   apply (wp | simp)+
  done

lemma thread_set_timeout_fault_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some (Timeout badge))) t \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply (rule valid_irq_handlers_lift)
    apply wp
    apply clarsimp
    apply (subst caps_of_state_after_update)
     apply (clarsimp simp: ran_tcb_cap_cases)
    apply simp
   apply (wp | simp)+
  done

lemma thread_set_timeout_fault_invs[wp]:
 "\<lbrace>invs\<rbrace> thread_set (tcb_fault_update (\<lambda>_. Some (Timeout badge))) tptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invs_def valid_pspace_def valid_state_def ran_tcb_cap_cases valid_fault_def
           wp: thread_set_refs_trivial thread_set_hyp_refs_trivial thread_set_valid_objs_triv
               thread_set_iflive_trivial thread_set_zombies_trivial thread_set_valid_ioc_trivial
               thread_set_valid_idle_trivial thread_set_only_idle thread_set_ifunsafe_trivial
               thread_set_global_refs_triv valid_irq_node_typ thread_set_arch_caps_trivial
               thread_set_cap_refs_in_kernel_window thread_set_cap_refs_respects_device_region)

lemma send_fault_ipc_invs_timeout:
  "\<lbrace>invs and st_tcb_at active tptr and ex_nonz_cap_to tptr
    and (\<lambda>s. caps_of_state s (tptr, tcb_cnode_index 4) = Some cap)
    and K (is_ep_cap cap)\<rbrace>
      send_fault_ipc tptr cap (Timeout badge) canDonate \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: send_fault_ipc_def)
  apply (wpsimp wp: send_ipc_invs_for_timeout hoare_vcg_conj_lift)
                apply (wpsimp simp: thread_set_def set_object_def)+
  apply safe
     apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev)
    apply (rule ex_cap_to_after_update, assumption)
    apply (clarsimp simp: obj_at_def get_tcb_SomeD ran_tcb_cap_cases)
   apply (subst caps_of_state_after_update[simplified fun_upd_apply])
    apply (clarsimp simp: obj_at_def get_tcb_SomeD ran_tcb_cap_cases)
   apply (clarsimp simp: caps_of_state_tcb_index_trans tcb_cnode_map_def)
  done

lemma handle_timeout_Timeout_invs:
  "\<lbrace>invs and st_tcb_at active tptr\<rbrace>
     handle_timeout tptr (Timeout badge)  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: handle_timeout_def)
  apply (wpsimp simp: handle_timeout_def ran_tcb_cap_cases
      thread_set_def valid_fault_def
      wp: thread_set_invs_trivial send_fault_ipc_invs_timeout)
  apply (case_tac "tcb_timeout_handler y"; clarsimp)
  apply (auto simp: tcb_cnode_map_def caps_of_state_tcb_index_trans)
  apply (drule invs_iflive)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  apply (drule (1) if_live_then_nonz_capD2)
  apply (fastforce simp: live_def split: thread_state.splits)
  by simp
thm end_timeslice_def
lemma end_timeslice_invs:
  "\<lbrace>invs and ct_active\<rbrace>
      end_timeslice t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: end_timeslice_def ct_in_state_def
          wp: handle_timeout_Timeout_invs hoare_drop_imp)
  done

lemma invs_valid_refills:
  "\<lbrakk> invs s; ko_at (SchedContext sc n) scptr s\<rbrakk> \<Longrightarrow> Suc 0 \<le> length (sc_refills sc)"
  by (clarsimp dest!: invs_valid_objs elim!: obj_at_valid_objsE simp: valid_obj_def valid_sched_context_def)

lemma sched_context_nonref_update_invs[wp]:
  "\<lbrace> invs and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n) scp \<rbrace>
    set_sched_context scp (sc\<lparr> sc_period := period, sc_refill_max := m, sc_refills := r0#rs\<rparr>)
      \<lbrace> \<lambda>_. invs \<rbrace> "
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs)
  apply (intro conjI)
    apply (erule (1) obj_at_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_sched_context_def)
   apply (clarsimp simp: if_live_then_nonz_cap_def)
   apply (drule_tac x=scp in spec)
   apply (clarsimp simp: obj_at_def live_sc_def live_def)
  apply (drule obj_at_state_refs_ofD)
  by (clarsimp simp: refs_of_def fun_upd_def[symmetric] fun_upd_idem simp del: refs_of_simps refs_of_defs)

lemma sched_context_refill_update_invs:
  "\<lbrace> invs and obj_at (\<lambda>ko. \<exists>n. ko = SchedContext sc n) scp \<rbrace>
    set_sched_context scp (sc\<lparr> sc_refills := r0#rs\<rparr>)
      \<lbrace> \<lambda>_. invs \<rbrace> "
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs)
  apply (intro conjI)
    apply (erule (1) obj_at_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_sched_context_def)
   apply (clarsimp simp: if_live_then_nonz_cap_def)
   apply (drule_tac x=scp in spec)
   apply (clarsimp simp: obj_at_def live_sc_def live_def)
  apply (drule obj_at_state_refs_ofD)
  by (clarsimp simp: refs_of_def fun_upd_def[symmetric] fun_upd_idem simp del: refs_of_simps refs_of_defs)

lemma update_sched_context_sc_consumed_update_invs:
  "\<lbrace> invs \<rbrace> update_sched_context scp (sc_consumed_update f)
      \<lbrace> \<lambda>_. invs \<rbrace> "
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
            wp: update_sched_context_valid_objs_same
                update_sched_context_refs_of_same valid_irq_node_typ)

lemma update_sched_context_sc_refills_update_invs:
  "\<lbrace> invs and K (\<forall>ls. 1 \<le> length ls \<longrightarrow> 1 \<le> length (f ls))\<rbrace>
     update_sched_context scp (sc_refills_update f)
      \<lbrace> \<lambda>_. invs \<rbrace> "
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def valid_sched_context_def
            simp_del: refs_of_defs
            wp: update_sched_context_valid_objs_same
                update_sched_context_refs_of_same valid_irq_node_typ)

lemma sc_consumed_add_invs:
  "\<lbrace> invs \<rbrace> update_sched_context scp (\<lambda>sc. sc\<lparr>sc_consumed := sc_consumed sc + consumed\<rparr>)
      \<lbrace> \<lambda>_. invs \<rbrace> "
  by (wpsimp simp: invs_def valid_state_def valid_pspace_def simp_del: refs_of_defs
            wp: update_sched_context_valid_objs_same
                update_sched_context_refs_of_same valid_irq_node_typ
                update_sched_context_iflive_same)

lemma refill_update_invs:
  "\<lbrace>invs\<rbrace> refill_update sc_ptr new_period new_budget new_max_refills \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: refill_update_def)
  apply (rule hoare_seq_ext [OF _ get_sched_context_sp])
  by (wpsimp, fastforce simp: obj_at_def)

lemma refill_budget_check_invs:
  "\<lbrace>invs\<rbrace> refill_budget_check sc_ptr usage capacity \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: refill_budget_check_def)
  apply (wpsimp simp: refill_budget_check_def refill_full_def
      refill_size_def split_def split_del: if_split
      wp: get_sched_context_wp static_imp_wp hoare_drop_imp
      hoare_vcg_all_lift hoare_vcg_if_lift2 update_sched_context_sc_refills_update_invs)
  apply (frule (1) invs_valid_refills)
  apply (clarsimp simp: min_budget_merge_length[THEN conjunct1, simplified])
  apply (intro conjI impI)
     apply (clarsimp simp: Let_def refills_budget_check_pos split: if_splits)+
  done

(* move to Invariants_AI *)
lemma ex_nonz_cap_to_consumed_time_update[iff]:
  "ex_nonz_cap_to p(consumed_time_update f s) = ex_nonz_cap_to p s"
  by (simp add: ex_nonz_cap_to_def)

crunch ct_active[wp]: refill_full ct_active

lemma refill_split_check_ex_nonz_cap_to_ct[wp]:
    "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_split_check sc_ptr usage
       \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_split_check_def set_refills_def Let_def
      wp: get_sched_context_wp get_refills_wp hoare_drop_imp)

lemma refill_budget_check_ex_nonz_cap_to_ct[wp]:
    "\<lbrace>\<lambda>s. ex_nonz_cap_to (cur_thread s) s\<rbrace> refill_budget_check sc_ptr usage capacity
       \<lbrace>\<lambda>rv s. ex_nonz_cap_to (cur_thread s) s\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def is_round_robin_def refill_full_def
      wp: get_sched_context_wp get_refills_wp hoare_drop_imp hoare_vcg_if_lift2 split_del: if_split)

crunch ct_active[wp]: tcb_sched_action, reschedule_required, tcb_release_remove ct_active

(*
lemma end_timeslice_active[wp]:
  "\<lbrace>ct_active\<rbrace> end_timeslice canTimeout \<lbrace> \<lambda>_ . ct_active\<rbrace>"
  by (wpsimp simp: end_timeslice_def wp: get_sched_context_wp)

lemma refill_budget_check_active[wp]:
  "\<lbrace>ct_active\<rbrace> refill_budget_check csc_ptr consumed capacity \<lbrace> \<lambda>_ . ct_active\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def
       wp: hoare_drop_imp get_sched_context_wp split_del: if_split)

lemma charge_budget_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> charge_budget capacity consumed canTimeout \<lbrace> \<lambda>_. ct_active\<rbrace>"
  by (wpsimp simp: charge_budget_def Let_def wp: get_sched_context_wp)
*)
lemma check_budget_ct_active[wp]:
  "\<lbrace>ct_active\<rbrace> check_budget \<lbrace> \<lambda>_ . ct_active\<rbrace>"
sorry(*   by (wpsimp simp: check_budget_def refill_capacity_def wp: get_refills_wp get_sched_context_wp)
*)

lemma refill_budget_check_active[wp]:
  "\<lbrace>ct_active\<rbrace> refill_budget_check csc_ptr consumed capacity \<lbrace> \<lambda>_ . ct_active\<rbrace>"
  by (wpsimp simp: refill_budget_check_def set_refills_def
       wp: hoare_drop_imp get_sched_context_wp split_del: if_split)

lemma charge_budget_invs:
  "\<lbrace>invs and ct_active\<rbrace>
     charge_budget capacity consumed canTimeout \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: charge_budget_def is_round_robin_def)
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_drop_imp hoare_vcg_all_lift refill_budget_check_invs
                 sc_consumed_add_invs update_sched_context_sc_refills_update_invs end_timeslice_invs
            split_del: if_split simp: set_object_def Let_def set_refills_def)

lemma check_budget_invs:
  "\<lbrace>invs and ct_active\<rbrace> check_budget \<lbrace>\<lambda>rv. invs\<rbrace>"
    by (wpsimp simp: check_budget_def refill_full_def refill_size_def
            wp: get_refills_inv hoare_drop_imp get_sched_context_wp charge_budget_invs)

crunch invs[wp]: tcb_release_remove invs

thm invoke_sched_control_configure_def
lemma invoke_sched_control_configure_invs[wp]:
  "\<lbrace>invs and valid_sched_control_inv i and ct_active\<rbrace>
         invoke_sched_control_configure i \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases i)
  apply (clarsimp simp: invoke_sched_control_configure_def split del: if_split)
  by (wpsimp simp: invoke_sched_control_configure_def valid_sched_control_inv_def split_def
      split_del: if_split
      wp: commit_time_invs update_sc_badge_invs hoare_vcg_if_lift2 check_budget_invs
         hoare_drop_imp get_sched_context_wp charge_budget_invs hoare_vcg_all_lift
         refill_update_invs)


text {* set_thread_state and schedcontext/schedcontrol invocations *}

lemma sts_idle_thread[wp]:
  "\<lbrace>\<lambda>s. t \<noteq> idle_thread s\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def sc_ntfn_sc_at_def obj_at_def)

lemma sts_sc_ntfn_sc_at:
  "\<lbrace>sc_ntfn_sc_at P scp\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. sc_ntfn_sc_at P scp\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def sc_ntfn_sc_at_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (fastforce simp: obj_at_def)
  done

lemma sts_sc_tcb_sc_at:
  "\<lbrace>sc_tcb_sc_at P scp\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. sc_tcb_sc_at P scp\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def sc_tcb_sc_at_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (fastforce simp add: pred_tcb_at_def obj_at_def)
  done

lemma sts_valid_sched_context_inv:
  "\<lbrace>(\<lambda>s. t \<noteq> cur_thread s) and valid_sched_context_inv sci\<rbrace>
      set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_context_inv sci\<rbrace>"
  apply (cases sci; clarsimp simp: )
      prefer 4
      apply (wpsimp+)[2]
    apply (wpsimp wp: valid_cap_typ set_object_wp gets_the_inv simp: set_thread_state_def
     | clarsimp simp: sc_ntfn_sc_at_def sc_tcb_sc_at_def sc_yf_sc_at_def dest!: get_tcb_SomeD split: cap.split
     | fastforce simp: valid_cap_def sc_ntfn_sc_at_def obj_at_def ran_tcb_cap_cases
                       fun_upd_def get_tcb_def is_tcb sc_tcb_sc_at_def pred_tcb_at_def
                 intro!: ex_cap_to_after_update
                 split: cap.split_asm option.splits kernel_object.split_asm)+
  done

lemma sts_valid_sched_control_inv:
  "\<lbrace>valid_sched_control_inv sci\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_sched_control_inv sci\<rbrace>"
  by (cases sci; wpsimp simp: obj_at_def  get_tcb_rev wp: sts_obj_at_impossible)

lemma decode_sched_context_inv_inv:
  "\<lbrace>P\<rbrace> decode_sched_context_invocation label sc_ptr excaps args \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_context_invocation_def whenE_def
               split del: if_split
            | wp_once hoare_drop_imp get_sk_obj_ref_inv get_sc_obj_ref_inv | wpcw)+
  done

lemma decode_sched_control_inv_inv:
  "\<lbrace>P\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: decode_sched_control_invocation_def whenE_def unlessE_def
                          split del: if_split
            | wp_once hoare_drop_imp get_sk_obj_ref_inv assertE_wp | wpcw)+
  done

lemma decode_sched_context_inv_wf:
  "\<lbrace>invs and sc_at sc_ptr and ex_nonz_cap_to sc_ptr and
     (\<lambda>s. ex_nonz_cap_to (cur_thread s) s) and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_context_invocation label sc_ptr excaps args
   \<lbrace>valid_sched_context_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_context_invocation_def whenE_def ethread_get_def
      get_sk_obj_ref_def get_tcb_obj_ref_def get_sc_obj_ref_def
      split_del: if_split
      wp: hoare_vcg_if_splitE get_simple_ko_wp
      thread_get_wp' get_sched_context_wp)
  apply (intro conjI; intro impI allI)
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (rule conjI; intro impI allI)
     apply simp
     apply (erule ballE[where x="hd excaps"])
      prefer 2
      apply (drule hd_in_set, simp)
     apply (erule_tac x=x in ballE)
      apply (clarsimp simp add: obj_at_def sc_ntfn_sc_at_def)
     apply clarsimp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     prefer 2
     apply (drule hd_in_set, simp)
    apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
   apply (frule invs_valid_global_refs, drule invs_valid_objs, clarsimp dest!: idle_no_ex_cap)
 apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (rule conjI; intro impI allI)
    apply simp
    apply (erule ballE[where x="hd excaps"])
     prefer 2
     apply (drule hd_in_set, simp)
    apply (erule_tac x=x in ballE)
     apply (clarsimp simp: obj_at_def sc_ntfn_sc_at_def is_sc_obj_def)
    apply clarsimp
   apply (erule ballE[where x="hd excaps"])
    prefer 2
    apply (drule hd_in_set, simp)
   apply (erule_tac x=x in ballE)
    prefer 2
    apply (drule hd_in_set, simp)
   apply (clarsimp simp: obj_at_def pred_tcb_at_def sc_tcb_sc_at_def)
  apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def is_sc_obj_def is_tcb pred_tcb_at_def sc_yf_sc_at_def)
  done

lemma decode_sched_control_inv_wf:
  "\<lbrace>invs and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> x) and
     (\<lambda>s. \<forall>x\<in>set excaps. \<forall>r\<in>zobj_refs x. ex_nonz_cap_to r s)\<rbrace>
     decode_sched_control_invocation label args excaps
   \<lbrace>valid_sched_control_inv\<rbrace>, -"
  apply (wpsimp simp: decode_sched_control_invocation_def whenE_def unlessE_def assertE_def split_del: if_split)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (erule ballE[where x="hd excaps"])
   prefer 2
   apply (drule hd_in_set, simp)
  apply (clarsimp simp add: valid_cap_def obj_at_def is_sc_obj_def split: cap.split_asm)
  apply (case_tac ko; simp)
  apply (clarsimp simp: valid_extra_refills_def refill_absolute_max_def MIN_REFILLS_def
                        us_to_ticks_mono[simplified mono_def] MIN_BUDGET_def
                        MIN_BUDGET_US_def ARM.kernelWCET_ticks_def)
  done


end