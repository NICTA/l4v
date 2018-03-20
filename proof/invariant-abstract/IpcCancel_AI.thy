(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory IpcCancel_AI
imports "./$L4V_ARCH/ArchSchedule_AI"
begin

context begin interpretation Arch .

requalify_facts
  arch_post_cap_deletion_pred_tcb_at

end

declare arch_post_cap_deletion_pred_tcb_at[wp]

lemma blocked_cancel_ipc_simple:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc ts t r \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: blocked_cancel_ipc_def | wp sts_st_tcb_at')+

lemma cancel_signal_simple:
  "\<lbrace>\<top>\<rbrace> cancel_signal t ntfn \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (simp add: cancel_signal_def | wp sts_st_tcb_at')+

crunch  typ_at: cancel_all_ipc "\<lambda>s. P (typ_at T p s)" (wp: crunch_wps mapM_x_wp)

lemma cancel_all_helper:
  " \<lbrace>valid_objs and
    (\<lambda>s. \<forall>t \<in> set queue. st_tcb_at (\<lambda>st. \<not> halted st) t s) \<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) queue
   \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [where S="set queue", simplified])
    apply (wp, simp, wp hoare_vcg_const_Ball_lift sts_st_tcb_at_cases, simp)
    apply (clarsimp elim: pred_tcb_weakenE)
    apply (erule(1) my_BallE)
    apply (clarsimp simp: st_tcb_def2)
    apply (frule(1) valid_tcb_objs)
    apply (clarsimp simp: valid_tcb_def valid_tcb_state_def
                          cte_wp_at_cases tcb_cap_cases_def
                   dest!: get_tcb_SomeD)
   apply simp+
  done


lemma set_thread_state_valid_objs_minorpre[wp]: (* FIXME: replace set_thread_state_valid_objs ? *)
 "\<lbrace>valid_objs and valid_tcb_state st\<rbrace>
  set_thread_state thread st
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp, simp, (wp set_object_valid_objs)+)
  apply (clarsimp simp: obj_at_def get_tcb_def
                 split: Structures_A.kernel_object.splits option.splits)
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_tcb_def a_type_def tcb_cap_cases_def)
  done


lemma cancel_all_ipc_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_ipc ptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp simp: cancel_all_ipc_def valid_tcb_state_def get_thread_state_def thread_get_def
                   get_ep_queue_def get_simple_ko_def get_object_def valid_ep_def
               wp: mapM_x_wp_inv)

(*
lemma unbind_notification_valid_objs_helper:
  "valid_ntfn ntfn s \<longrightarrow> valid_ntfn (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn None) s "
  by (clarsimp simp:  valid_ntfn_def
                  split: option.splits ntfn.splits)
*)

lemma get_ntfn_valid_ntfn_minor[wp]: (* FIXME: replace get_ntfn_valid_ntfn ? *)
  "\<lbrace> valid_objs \<rbrace>
   get_notification ntfn
   \<lbrace> valid_ntfn \<rbrace>"
  apply (wpsimp simp: get_simple_ko_def get_object_def wp_del: get_ntfn_valid_ntfn)
  apply (auto simp: valid_obj_def)
  done

lemma unbind_notification_valid_objs:
  "\<lbrace>valid_objs\<rbrace>
   unbind_notification ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: unbind_notification_def update_sk_obj_ref_def)
     apply (rule hoare_strengthen_post)
      apply (wpsimp simp: valid_ntfn_def split: ntfn.splits)+
  done


lemma possible_switch_to_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   possible_switch_to ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by wpsimp

lemma cancel_all_signals_valid_objs:
  "\<lbrace>valid_objs and (\<lambda>s. sym_refs (state_refs_of s))\<rbrace>
   cancel_all_signals ptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wpsimp simp: cancel_all_signals_def valid_tcb_state_def get_simple_ko_def get_object_def
                  wp: mapM_x_wp_inv)
  apply (auto simp: valid_obj_def valid_ntfn_def)
  done


lemma get_ep_queue_inv[wp]:
  "\<lbrace>P\<rbrace> get_ep_queue ep \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases ep, simp_all add: get_ep_queue_def)

lemma reply_unlink_tcb_st_tcb_at:
   assumes x: "P Inactive"
   shows
  "\<lbrace>\<lambda>s. st_tcb_at P t s (*\<and>
        (\<forall>r. kheap s rptr = Some (Reply r) \<longrightarrow> reply_tcb r = Some t \<longrightarrow> P Structures_A.Inactive)*)\<rbrace>
   reply_unlink_tcb rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: reply_unlink_tcb_def)
  apply (wpsimp simp: update_sk_obj_ref_def set_simple_ko_def set_object_def get_thread_state_def
                      thread_get_def   st_tcb_at_def obj_at_def x
                  wp: sts_st_tcb_at_cases get_object_wp get_simple_ko_wp)
  done

lemma cancel_all_ipc_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart"
  assumes y[simp]: "P Structures_A.Inactive" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cancel_all_ipc_def
  by (wpsimp wp: ep_cases_weak_wp mapM_x_wp' hoare_drop_imp sts_st_tcb_at_cases
              reply_unlink_tcb_st_tcb_at)

lemmas cancel_all_ipc_makes_simple[wp] =
  cancel_all_ipc_st_tcb_at[where P=simple, simplified]


lemma unbind_notification_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_notification t' \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: unbind_notification_def update_sk_obj_ref_def)

lemma unbind_maybe_notification_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> unbind_maybe_notification r \<lbrace>\<lambda>rv. st_tcb_at P t \<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def update_sk_obj_ref_def get_sk_obj_ref_def)


lemma cancel_all_signals_st_tcb_at:
  assumes x[simp]: "P Structures_A.Restart" shows
  "\<lbrace>st_tcb_at P t\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  unfolding cancel_all_signals_def unbind_maybe_notification_def
  by (wp ntfn_cases_weak_wp mapM_x_wp' sts_st_tcb_at_cases
         hoare_drop_imps unbind_notification_st_tcb_at
    | simp | wpc)+


lemmas cancel_all_signals_makes_simple[wp] =
       cancel_all_signals_st_tcb_at[where P=simple, simplified]


lemma get_blocking_object_inv[wp]:
  "\<lbrace>P\<rbrace> get_blocking_object st \<lbrace>\<lambda>_. P\<rbrace>"
  by (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)

lemma reply_unlink_sc_st_tcb_at:
  "\<lbrace>st_tcb_at P t\<rbrace> reply_unlink_sc scp rp \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def set_sc_obj_ref_def update_sk_obj_ref_def
                  wp: get_simple_ko_wp)
  done


thm reply_remove_def reply_unlink_tcb_def
lemma reply_remove_st_tcb_at[wp]:
   assumes x: "P Inactive"
   shows
  "\<lbrace>\<lambda>s. st_tcb_at P t s \<rbrace>
   reply_remove rptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_remove_def x split_del: if_split cong: conj_cong
 wp: hoare_vcg_if_lift2 hoare_drop_imp reply_unlink_sc_st_tcb_at reply_unlink_tcb_st_tcb_at)

lemma set_thread_state_st_tcb_at:  (* FIXME: is the precondition necessary? *)
  "\<lbrace>\<lambda>s. st_tcb_at P t' s \<and> (t = t' \<longrightarrow> P st)\<rbrace> set_thread_state t st
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  by (wpsimp simp: set_thread_state_def set_object_def pred_tcb_at_def obj_at_def)

lemma blocked_ipc_st_tcb_at_general:  (* FIXME: is the precondition necessary? *)
   assumes x: "P Inactive" shows
  "\<lbrace>\<lambda>s. st_tcb_at P t' s\<rbrace>
   blocked_cancel_ipc st t rptropt
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wpsimp simp: set_simple_ko_def set_object_def get_ep_queue_def get_simple_ko_def
                      get_object_def get_blocking_object_def x
                  wp: set_thread_state_st_tcb_at weak_if_wp reply_unlink_tcb_st_tcb_at)
  done

lemma cancel_signal_st_tcb_at_general:
  "\<lbrace>st_tcb_at P t' and K (t = t' \<longrightarrow> (P Structures_A.Running \<and> P Structures_A.Inactive))\<rbrace>
     cancel_signal t ntfn
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (wp sts_st_tcb_at_cases ntfn_cases_weak_wp static_imp_wp)
  apply simp
  done


lemma sched_context_maybe_unbind_ntfn_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_maybe_unbind_ntfn ntfnptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
   by (wpsimp simp: sched_context_maybe_unbind_ntfn_def sched_context_unbind_ntfn_def
                    set_sc_obj_ref_def update_sk_obj_ref_def get_sc_obj_ref_def get_sk_obj_ref_def)

lemma sched_context_unbind_ntfn_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_ntfn scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_ntfn_def set_sc_obj_ref_def update_sk_obj_ref_def
                   get_sc_obj_ref_def)

lemma sched_context_update_consumed_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_update_consumed scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def)

lemma set_message_info_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_message_info a b \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
   by (wpsimp simp: set_message_info_def)

lemma complete_yield_to_st_tcb_at[wp]:
   assumes x[simp]: "P Running" shows
  "\<lbrace>st_tcb_at P t\<rbrace> complete_yield_to scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: complete_yield_to_def set_sc_obj_ref_def set_consumed_def
                   get_sc_obj_ref_def
 wp: set_thread_state_st_tcb_at set_message_info_st_tcb_at hoare_drop_imp)

lemma sched_context_unbind_yield_from_st_tcb_at[wp]:
   assumes x[simp]: "P Running" shows
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_yield_from scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_yield_from_def)

lemma sched_context_clear_replies_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_clear_replies scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_clear_replies_def reply_unlink_sc_def set_sc_obj_ref_def
                   update_sk_obj_ref_def
               wp: mapM_x_wp' hoare_drop_imp)

lemma sched_context_unbind_all_tcbs_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> sched_context_unbind_all_tcbs scptr \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def sched_context_unbind_tcb_def set_sc_obj_ref_def
               wp: hoare_drop_imp)

lemma fast_finalise_misc[wp]:
"\<lbrace>st_tcb_at simple t \<rbrace> fast_finalise a b \<lbrace>\<lambda>_. st_tcb_at simple t\<rbrace>"
  apply (case_tac a,simp_all)
  by (wpsimp simp: when_def reply_clear_tcb_def
          wp: reply_unlink_tcb_st_tcb_at hoare_drop_imp get_simple_ko_wp)+

locale IpcCancel_AI =
    fixes state_ext :: "('a::state_ext) itself"
    assumes arch_post_cap_deletion_typ_at[wp]:
      "\<And>P T p. \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
    assumes arch_post_cap_deletion_idle_thread[wp]:
      "\<And>P. \<lbrace>\<lambda>(s :: 'a state). P (idle_thread s)\<rbrace> arch_post_cap_deletion acap \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"

(* Fixme: Commented due to the change of reply_remove_st_tcb_at
crunch st_tcb_at_simple[wp]: reply_cancel_ipc "st_tcb_at simple t"
  (wp: crunch_wps select_wp sts_st_tcb_at_cases thread_set_no_change_tcb_state maybeM_inv
   simp: crunch_simps unless_def fast_finalise.simps)
 *)

lemma scyf_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_sc_obj_ref sc_yield_from_update sc tcb \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (simp add: set_sc_obj_ref_def set_object_def)
  apply wp
  done

lemma reply_remove_tcb_st_tcb_at_simple[wp]:
  "\<lbrace>st_tcb_at simple t\<rbrace> reply_remove_tcb tp \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  by (wpsimp simp: reply_remove_tcb_def wp: hoare_drop_imp gts_inv hoare_vcg_all_lift)

lemma reply_cancel_ipc_st_tcb_at_simple[wp]:
  "\<lbrace>st_tcb_at simple t\<rbrace> reply_cancel_ipc tp rpopt \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (wpsimp simp: reply_cancel_ipc_def thread_set_def wp: set_object_wp)
  by (clarsimp dest!: get_tcb_SomeD simp: pred_tcb_at_def obj_at_def)

lemma cancel_ipc_simple [wp]:
  "\<lbrace>\<top>\<rbrace> cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
         apply (wp hoare_strengthen_post [OF blocked_cancel_ipc_simple]
                   hoare_strengthen_post [OF cancel_signal_simple]
                   hoare_strengthen_post
                      [OF reply_cancel_ipc_st_tcb_at_simple [where t=t]]
                   sts_st_tcb_at_cases
                   hoare_drop_imps | (rule pred_tcb_weakenE, fastforce)
                        | clarsimp elim!: pred_tcb_weakenE pred_tcb_at_tcb_at)+
  done

lemma reply_remove_typ_at[wp]:
  (* RT: check the precondition (can't be correct); might need to change the lemma below *)
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> reply_remove r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: reply_remove_def wp: reply_unlink_tcb_typ_at hoare_drop_imp)

lemma blocked_cancel_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> blocked_cancel_ipc st t r \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def wp: reply_unlink_tcb_typ_at)


lemma blocked_cancel_ipc_tcb_at [wp]:
  "\<lbrace>tcb_at t\<rbrace> blocked_cancel_ipc st t' r \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

context IpcCancel_AI begin
(*
lemma maybeM_typ_at[wp]:
  "\<forall>a. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f a \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace> \<Longrightarrow>
     \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> maybeM f opt \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (wpsimp simp: maybeM_def)
  done*)

crunch typ_at[wp]: cancel_ipc, reply_cancel_ipc
                   "\<lambda>(s::'a state). P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE select_wp maybeM_inv
     simp: crunch_simps unless_def)

crunch typ_at[wp]: get_notification
                   "\<lambda>(s::'a state). P (typ_at T p s)"
  (wp: crunch_wps hoare_vcg_if_splitE select_wp
     simp: crunch_simps unless_def)

lemma unbind_maybe_notification_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
     unbind_maybe_notification t \<lbrace>\<lambda>_ (s::'a state). P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: unbind_maybe_notification_def)

lemma cancel_ipc_tcb [wp]:
  "\<lbrace>tcb_at t\<rbrace> cancel_ipc t' \<lbrace>\<lambda>rv. (tcb_at t) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

lemma gbep_ret:
  "\<lbrakk> st = Structures_A.BlockedOnReceive epPtr r \<or>
     st = Structures_A.BlockedOnSend epPtr p \<rbrakk> \<Longrightarrow>
  get_blocking_object st = return epPtr"
  by (auto simp add: get_blocking_object_def ep_blocked_def assert_opt_def)


lemma st_tcb_at_valid_st2:
  "\<lbrakk> st_tcb_at (op = st) t s; valid_objs s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def get_tcb_def pred_tcb_at_def
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done


definition
 "emptyable \<equiv> \<lambda>p s. (tcb_at (fst p) s \<and> snd p = tcb_cnode_index 2) \<longrightarrow>
                          st_tcb_at halted (fst p) s"


locale delete_one_abs =
  fixes state_ext_type :: "('a :: state_ext) itself"
  assumes delete_one_invs:
    "\<And>p. \<lbrace>invs and emptyable p\<rbrace> (cap_delete_one p :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"

  assumes delete_one_deletes:
    "\<lbrace>\<top>\<rbrace> (cap_delete_one sl :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"

  assumes delete_one_caps_of_state:
    "\<And>P p. \<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
                  \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
             (cap_delete_one p :: (unit,'a) s_monad)
            \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"

lemma ep_redux_simps2:
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   valid_ep (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
            | a # list \<Rightarrow> update_ep_queue ep xs)
     = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "ep \<noteq> Structures_A.IdleEP \<Longrightarrow>
   ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                   | a # list \<Rightarrow> update_ep_queue ep xs)
     = (set xs \<times> {case ep of Structures_A.SendEP xs \<Rightarrow> EPSend | Structures_A.RecvEP xs \<Rightarrow> EPRecv})"
 by (cases ep, simp_all cong: list.case_cong add: ep_redux_simps)+


lemma gbi_ep_sp:
  "\<lbrace>P\<rbrace>
     get_blocking_object st
   \<lbrace>\<lambda>ep. P and K ((\<exists>r. st = Structures_A.BlockedOnReceive ep r)
                    \<or> (\<exists>d. st = Structures_A.BlockedOnSend ep d))\<rbrace>"
  apply (cases st, simp_all add: get_blocking_object_def ep_blocked_def assert_opt_def)
   apply (wp | simp)+
  done


lemma get_epq_sp:
  "\<lbrace>P\<rbrace>
  get_ep_queue ep
  \<lbrace>\<lambda>q. P and K (ep \<in> {Structures_A.SendEP q, Structures_A.RecvEP q})\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (cases ep)
  apply (wp|simp)+
  done

crunches reply_unlink_tcb
 for aligned[wp]: pspace_aligned
 and distinct[wp]: pspace_distinct
 and iflive[wp]: if_live_then_nonz_cap
 and cte_wp_at[wp]: "cte_wp_at P c"
 and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
 and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
 and no_cdt[wp]: "\<lambda>s. P (cdt s)"
 and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
 and cur_sc[wp]: "\<lambda>s. P (cur_sc s)"
 and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
 and hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
 and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
 and valid_irq_handlers[wp]: valid_irq_handlers
 and valid_global_objs[wp]: "valid_global_objs"
 and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
 and valid_arch_caps[wp]: "valid_arch_caps"
 and ifunsafe[wp]: "if_unsafe_then_cap"
 and valid_arch[wp]: "valid_arch_state"
 and valid_irq_states[wp]: "valid_irq_states"
 and vms[wp]: "valid_machine_state"
 and valid_vspace_objs[wp]: "valid_vspace_objs"
 and valid_global_refs[wp]: "valid_global_refs"
 and v_ker_map[wp]: "valid_kernel_mappings"
 and equal_mappings[wp]: "equal_kernel_mappings"
 and valid_asid_map[wp]: "valid_asid_map"
 and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
 and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
 and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
 and pspace_respects_device_region[wp]: "pspace_respects_device_region"
 and cur_tcb[wp]: "cur_tcb"
 and valid_mdb[wp]: "valid_mdb"
 and valid_ioc[wp]: "valid_ioc"
 and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: Let_def wp: hoare_drop_imps)

lemma sc_at[wp]: "\<lbrace>sc_at sc_ptr\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. sc_at sc_ptr\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  by (clarsimp simp: obj_at_def is_sc_obj_def)

lemma valid_idle[wp]:
  "\<lbrace>valid_idle and (\<lambda>s. reply_tcb_reply_at (\<lambda>rt. rt = Some t \<and> t \<noteq> idle_thread s) rp s)\<rbrace>
     reply_unlink_tcb rp \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  by (clarsimp simp: valid_idle_def reply_tcb_reply_at_def obj_at_def pred_tcb_at_def)

lemma only_idle[wp]:
  "\<lbrace>only_idle
    and (\<lambda>s. reply_tcb_reply_at (\<lambda>rt. rt = Some t \<and> (st_tcb_at idle t s \<longrightarrow> t = idle_thread s)) rp s)\<rbrace>
        reply_unlink_tcb rp \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp sts_only_idle)
  by (clarsimp simp: only_idle_def pred_tcb_at_def reply_tcb_reply_at_def obj_at_def)

lemma zombie_final[wp]: "\<lbrace>zombies_final\<rbrace> reply_unlink_tcb rp \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def set_simple_ko_def
            wp: set_object_wp hoare_drop_imp get_simple_ko_wp)
  apply (rule zombies_kheap_update, simp)
  by (clarsimp simp: obj_at_def is_reply)


lemma blocked_cancel_ipc_invs:
  notes reply_unlink_tcb_iflive[wp del]
shows
  "\<lbrace>invs and st_tcb_at (op = st) t and
       K (\<exists>x y. (st = BlockedOnSend x y \<and> r = None ) \<or> (st = BlockedOnReceive x r)) \<rbrace>
      blocked_cancel_ipc st t r \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: blocked_cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gbi_ep_sp])
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext [OF _ get_epq_sp])
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ sts_only_idle)
   apply (clarsimp simp add: valid_tcb_state_def)
  (* apply (fastfor ce elim!: delta_sym_refs pred_tcb_weaken_strongerE
                 simp: obj_at_def is_ep_def2 idle_not_queued get_refs_def2
                 dest: idle_only_sc_refs
                 split: if_split_asm)[1]
  done*)sorry

lemma cancel_signal_invs:
  "\<lbrace>invs and st_tcb_at (op = (Structures_A.BlockedOnNotification ntfn)) t\<rbrace>
  cancel_signal t ntfn
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_signal_def
                   invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfna", simp_all)[1]
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle
           | simp add: valid_tcb_state_def refs_of_ntfn_def
           | wpc)+
  apply (clarsimp simp: refs_of_ntfn_def ep_redux_simps cong: list.case_cong if_cong)
  apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def live_ntfn_def)+)
  apply (frule ko_at_state_refs_ofD)
  apply (frule st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE, clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (case_tac ntfna)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp split:option.split)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)+
   apply (fastforce dest: refs_in_get_refs symreftype_inverse')
  apply (fastforce simp: obj_at_def is_ntfn idle_not_queued
                   dest: idle_only_sc_refs elim: pred_tcb_weakenE)
  done

lemma reply_cancel_ipc_invs:
  assumes delete: "\<And>p. \<lbrace>invs and emptyable p\<rbrace>
                        (cap_delete_one p :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  shows           "\<lbrace>invs\<rbrace> (reply_cancel_ipc t r :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply (wpsimp wp: delete select_wp)

sorry (*
  apply (rule_tac Q="\<lambda>rv. invs" in hoare_post_imp)
   apply (fastforce simp: emptyable_def dest: reply_slot_not_descendant)
  apply (wp thread_set_invs_trivial)
   apply (auto simp: tcb_cap_cases_def)+
  done *)


lemma (in delete_one_abs) cancel_ipc_invs[wp]:
  "\<lbrace>invs\<rbrace> (cancel_ipc t :: (unit,'a) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac state, simp_all)
        apply (auto intro!: hoare_weaken_pre [OF return_wp]
                            hoare_weaken_pre [OF blocked_cancel_ipc_invs]
                            hoare_weaken_pre [OF cancel_signal_invs]
                            hoare_weaken_pre [OF reply_cancel_ipc_invs]
                            delete_one_invs
                     elim!: pred_tcb_weakenE)
  sorry

context IpcCancel_AI begin

lemma cancel_ipc_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> cancel_ipc p \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma cancel_ipc_cte_at[wp]:
  "\<lbrace>cte_at p\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. (cte_at p) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cte_at_typ)

end

lemma valid_ep_queue_subset:
  "\<lbrace>\<lambda>s. valid_ep ep s\<rbrace>
     get_ep_queue ep
   \<lbrace>\<lambda>queue s. valid_ep (case (remove1 t queue) of [] \<Rightarrow> Structures_A.endpoint.IdleEP
                       | a # list \<Rightarrow> update_ep_queue ep (remove1 t queue)) s\<rbrace>"
  apply (simp add: get_ep_queue_def)
  apply (case_tac ep, simp_all)
   apply wp
   apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  apply wp
  apply (clarsimp simp: ep_redux_simps2 valid_ep_def)
  done

lemma blocked_cancel_ipc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> blocked_cancel_ipc st t r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: blocked_cancel_ipc_def)
  apply (wp get_simple_ko_valid[where f=Endpoint, simplified valid_ep_def2[symmetric]]
            valid_ep_queue_subset
         | simp only: valid_inactive simp_thms
                cong: imp_cong
         | rule hoare_drop_imps
         | clarsimp)+
  sorry


lemma cancel_signal_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> cancel_signal t ntfnptr \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: cancel_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp set_simple_ko_valid_objs
       | simp only: valid_inactive
       | simp
       | wpc)+
  apply (clarsimp simp: ep_redux_simps cong: list.case_cong)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (auto split: option.splits list.splits)
done


lemma tcb_in_valid_state:
  "\<lbrakk> st_tcb_at P t s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>st. P st \<and> valid_tcb_state st s"
  apply (clarsimp simp add: valid_objs_def pred_tcb_at_def obj_at_def)
  apply (erule my_BallE, erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  apply blast
  done


lemma no_refs_simple_strg:
  "st_tcb_at simple t s \<and> P {} \<longrightarrow> st_tcb_at (\<lambda>st. P (tcb_st_refs_of st)) t s"
(*  by (fastforce elim!: pred_tcb_weakenE)+ *) sorry (* is this true? *)

lemma schedule_tcb_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> schedule_tcb tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

crunch it[wp]: set_thread_state "\<lambda>(s::det_ext state). P (idle_thread s)"
  (wp: crunch_wps select_wp simp: unless_def crunch_simps)


lemma cancel_all_ipc_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_all_ipc tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_all_ipc_def set_thread_state_def reply_unlink_tcb_def
               wp: mapM_x_wp' hoare_drop_imp)

lemma cancel_signal_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_signal tcb_ptr ntfnptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_signal_def set_thread_state_def set_simple_ko_def set_object_def
                   get_object_def get_simple_ko_def)

lemma cancel_all_signals_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> cancel_all_signals tcb_ptr
      \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: cancel_all_signals_def set_thread_state_def get_simple_ko_def get_object_def
               wp: mapM_x_wp')

crunch it[wp]: unbind_notification "\<lambda>(s::det_ext state). P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps)

crunch it[wp]: fast_finalise "\<lambda>(s::det_ext state). P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps)

context IpcCancel_AI begin
lemma reply_cancel_ipc_it[wp]: (* broken due to rebase *)
  "\<lbrace>\<lambda>(s::'a state). P (idle_thread s)\<rbrace> reply_cancel_ipc param_a param_b
    \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  sorry
(*
crunch it[wp]: reply_cancel_ipc  "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp maybeM_inv simp: unless_def crunch_simps)
*)

lemma blocked_cancel_ipc_it[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> blocked_cancel_ipc param_a param_b r
    \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: blocked_cancel_ipc_def set_thread_state_def reply_unlink_tcb_def
               wp: hoare_drop_imp)

crunch it[wp]: cancel_ipc "\<lambda>(s::'a state). P (idle_thread s)"
  (wp: maybeM_inv)
end

lemma (in delete_one_abs) reply_cancel_ipc_no_reply_cap[wp]:
  notes hoare_pre [wp_pre del]
  shows "\<lbrace>invs and tcb_at t\<rbrace> (reply_cancel_ipc t r:: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: reply_cancel_ipc_def)
  apply wp
sorry (*
     apply (rule_tac Q="\<lambda>rvp s. cte_wp_at (\<lambda>c. c = cap.NullCap) x s \<and>
                                (\<forall>sl. sl \<noteq> x \<longrightarrow>
                                  caps_of_state s sl \<noteq> Some (cap.ReplyCap t False))"
                  in hoare_strengthen_post)
      apply (wp hoare_vcg_conj_lift hoare_vcg_all_lift
                delete_one_deletes delete_one_caps_of_state)
     apply (clarsimp simp: has_reply_cap_def cte_wp_at_caps_of_state)
     apply (case_tac "(aa, ba) = (a, b)", simp_all)[1]
    apply (wp hoare_vcg_all_lift select_wp | simp del: split_paired_All)+
  apply (rule_tac Q="\<lambda>_ s. invs s \<and> tcb_at t s" in hoare_post_imp)
   apply (erule conjE)
   apply (frule(1) reply_cap_descends_from_master)
   apply (auto dest: reply_master_no_descendants_no_reply[rotated -1])
  apply (wp thread_set_invs_trivial | clarsimp simp: tcb_cap_cases_def)+
  done*) (* RT: the statement is probably wrong *)


lemma (in delete_one_abs) cancel_ipc_no_reply_cap[wp]:
  shows "\<lbrace>invs and tcb_at t\<rbrace> (cancel_ipc t :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: cancel_ipc_def)
sorry
(*  apply (wpsimp wp: hoare_post_imp [OF invs_valid_reply_caps]
                  reply_cancel_ipc_no_reply_cap
                  cancel_signal_invs cancel_signal_st_tcb_at_general
                  blocked_cancel_ipc_invs blocked_ipc_st_tcb_at_general
        | strengthen reply_cap_doesnt_exist_strg)+
   apply (rule_tac Q="\<lambda>rv. st_tcb_at (op = rv) t and invs" in hoare_strengthen_post)
    apply (wpsimp wp: gts_st_tcb)
   apply (fastforce simp: invs_def valid_state_def st_tcb_at_tcb_at
                   elim!: pred_tcb_weakenE)+
  done *) (* RT: the statement is probably wrong *)


lemma (in delete_one_abs) suspend_invs[wp]:
  "\<lbrace>invs and tcb_at t and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   (suspend t :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. invs\<rbrace>"
sorry (*  apply (simp add: suspend_def)
  apply (wp sts_invs_minor cancel_ipc_invs cancel_ipc_no_reply_cap
       | strengthen no_refs_simple_strg | simp)+
  done *)

context IpcCancel_AI begin

lemma suspend_typ_at [wp]:
  "\<lbrace>\<lambda>(s::'a state). P (typ_at T p s)\<rbrace> suspend t \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: suspend_def)


lemma suspend_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> suspend tcb \<lbrace>\<lambda>_. (valid_cap c) :: 'a state \<Rightarrow> bool\<rbrace>"
  by (wp valid_cap_typ)


lemma suspend_tcb[wp]:
  "\<lbrace>tcb_at t'\<rbrace> suspend t \<lbrace>\<lambda>rv. (tcb_at t')  :: 'a state \<Rightarrow> bool\<rbrace>"
  by (simp add: tcb_at_typ) wp

end

declare if_cong [cong del]


crunch cte_wp_at[wp]: blocked_cancel_ipc "cte_wp_at P p"
  (wp: crunch_wps maybeM_inv)

crunch cte_wp_at[wp]: cancel_signal "cte_wp_at P p"
  (wp: crunch_wps)

crunch cte_wp_at[wp]: reply_remove_tcb "cte_wp_at P p"
  (wp: crunch_wps)

locale delete_one_pre =
  assumes delete_one_cte_wp_at_preserved:
    "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
     \<lbrace>cte_wp_at P sl\<rbrace> (cap_delete_one sl' :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"


lemma (in delete_one_pre) reply_cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (reply_cancel_ipc t r:: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wpsimp wp: select_wp delete_one_cte_wp_at_preserved)
   apply (rule_tac Q="\<lambda>_. cte_wp_at P p" in hoare_post_imp, clarsimp)
   apply (wpsimp wp: thread_set_cte_wp_at_trivial simp: tcb_cap_cases_def)
  apply assumption
  done


lemma (in delete_one_pre) cancel_ipc_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (cancel_ipc t :: (unit,det_ext) s_monad) \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_pre)
   apply (wp reply_cancel_ipc_cte_wp_at_preserved | wpcw | simp)+
  done

(* RT: FIXME move *)
crunch cte_wp_at[wp]: get_sched_context "cte_wp_at P c"

(* RT: FIXME move *)
lemma set_sc_yield_from_update_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_sc_obj_ref sc_yield_from_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by wp

lemma (in delete_one_pre) suspend_cte_wp_at_preserved:
  "(\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap) \<Longrightarrow>
  \<lbrace>cte_wp_at P p\<rbrace> (suspend tcb :: (unit,det_ext) s_monad) \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (simp add: suspend_def) (wpsimp wp: cancel_ipc_cte_wp_at_preserved)


(* FIXME - eliminate *)
lemma obj_at_exst_update:
  "obj_at P p (trans_state f s) = obj_at P p s"
  by (rule more_update.obj_at_update)


lemma set_thread_state_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> set_thread_state p ts \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding set_thread_state_def set_object_def
  by (wpsimp simp: pred_tcb_at_def obj_at_def get_tcb_def)


lemma reply_unlink_tcb_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> reply_unlink_tcb rptr \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: reply_unlink_tcb_def update_sk_obj_ref_def wp: hoare_drop_imp)

crunch bound_tcb_at[wp]: cancel_all_ipc, empty_slot, is_final_cap, get_cap "bound_tcb_at P t"
  (wp: mapM_x_wp_inv)


lemma fast_finalise_bound_tcb_at: (* broken due to rebase *)
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>tt b. cap = ReplyCap tt) \<rbrace> fast_finalise cap final \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
(*  by (case_tac cap, simp_all) *) sorry


lemma get_cap_reply_cap_helper:
  "\<lbrace>\<lambda>s. \<exists>t b. Some (ReplyCap t) = caps_of_state s slot \<rbrace> get_cap slot \<lbrace>\<lambda>rv s. \<exists>t b. rv = ReplyCap t\<rbrace>"
  by (auto simp: valid_def get_cap_caps_of_state[symmetric])


lemma cap_delete_one_bound_tcb_at:
  "\<lbrace>\<lambda>s. bound_tcb_at P t s \<and> (\<exists>t b. caps_of_state s c = Some (ReplyCap t)) \<rbrace>
      cap_delete_one c \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: cap_delete_one_def unless_def
               wp: fast_finalise_bound_tcb_at hoare_vcg_if_lift2 get_cap_reply_cap_helper
                   hoare_drop_imp)


lemma caps_of_state_tcb_index_trans:
  "\<lbrakk>get_tcb p s = Some tcb \<rbrakk> \<Longrightarrow> caps_of_state s (p, tcb_cnode_index n) = (tcb_cnode_map tcb) (tcb_cnode_index n)"
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: caps_of_state_def)
  apply (safe)
   apply (clarsimp simp: get_object_def get_cap_def)
   apply (simp add:set_eq_iff)
   apply (drule_tac x=cap in spec)
   apply (drule_tac x=s in spec)
   apply (clarsimp simp: in_monad)
  apply (clarsimp simp: get_cap_def get_object_def)
  apply (rule ccontr)
  apply (drule not_sym)
  apply (auto simp: set_eq_iff in_monad)
  done


lemma descendants_of_nullcap:
  "\<lbrakk>descendants_of (a, b) (cdt s) \<noteq> {}; valid_mdb s \<rbrakk> \<Longrightarrow> caps_of_state s (a, b) \<noteq> Some NullCap"
  apply clarsimp
  apply (drule_tac cs="caps_of_state s" and p="(a,b)" and m="(cdt s)" in mdb_cte_at_Null_descendants)
   apply (clarsimp simp: valid_mdb_def2)+
  done

lemma reply_cancel_ipc_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t and valid_mdb and valid_objs and tcb_at p \<rbrace>
    reply_cancel_ipc p r
   \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  unfolding reply_cancel_ipc_def
  apply (wpsimp wp: cap_delete_one_bound_tcb_at select_inv select_wp)
   apply (rule_tac Q="\<lambda>_. bound_tcb_at P t and valid_mdb and valid_objs and tcb_at p" in  hoare_strengthen_post)
    apply (wpsimp wp: thread_set_no_change_tcb_pred thread_set_mdb)
(*     apply (fastforce simp:tcb_cap_cases_def)
    apply (wpsimp wp: thread_set_valid_objs_triv simp: tcb_cap_cases_def)
   apply clarsimp
   apply (frule valid_mdb_impl_reply_masters)
   apply (clarsimp simp: reply_masters_mdb_def)
   apply (spec p)
   apply (spec "tcb_cnode_index 2")
   apply (spec p)
   apply (clarsimp simp:tcb_at_def)
   apply (frule(1) valid_tcb_objs)
   apply (clarsimp simp: valid_tcb_def)
   apply (erule impE)
    apply (simp add: caps_of_state_tcb_index_trans tcb_cnode_map_def)
    apply (clarsimp simp: tcb_cap_cases_def is_master_reply_cap_def split:cap.splits  )
    apply (subgoal_tac "descendants_of (p, tcb_cnode_index 2) (cdt s) \<noteq> {}")
     prefer 2
     apply simp
    apply (drule descendants_of_nullcap, simp)
    apply (simp add: caps_of_state_tcb_index_trans tcb_cnode_map_def)
   apply fastforce
  apply simp
  done *) sorry

lemma set_tcb_obj_ref_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> set_tcb_obj_ref param_a param_b param_c
     \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  sorry

lemma reply_remove_bound_tcb_at[wp]: "\<lbrace>bound_tcb_at P t\<rbrace> reply_remove r (* broken due to rebase *)
  \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  sorry

crunch bound_tcb_at[wp]: cancel_ipc "bound_tcb_at P t:: det_ext state \<Rightarrow> bool"
(ignore: set_object thread_set wp: mapM_x_wp_inv maybeM_inv)

lemma suspend_unlive:
  "\<lbrace>bound_tcb_at (op = None) t and valid_mdb and valid_objs and tcb_at t \<rbrace>
      suspend t
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) t\<rbrace>"
  apply (simp add: suspend_def set_thread_state_def set_object_def)
  apply (wp | simp only: obj_at_exst_update)+
  apply (simp add: obj_at_def)
(*  apply (rule_tac Q="\<lambda>_. bound_tcb_at (op = None) t" in hoare_strengthen_post)
  apply wp
  apply (auto simp: pred_tcb_def2 dest: refs_of_live)
  done *) sorry

definition bound_refs_of_tcb :: "'a state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> reftype) set"
where
  "bound_refs_of_tcb s t \<equiv> case kheap s t of
                              Some (TCB tcb) \<Rightarrow> get_refs TCBBound (tcb_bound_notification tcb)
                            | _ \<Rightarrow> {}"

lemma bound_refs_of_tcb_trans:
  "bound_refs_of_tcb (trans_state f s) x = bound_refs_of_tcb s x"
  by (clarsimp simp:bound_refs_of_tcb_def trans_state_def)

lemma cancel_all_invs_helper:
  "\<lbrace>all_invs_but_sym_refs
          and (\<lambda>s. (\<forall>x\<in>set q. ex_nonz_cap_to x s)
                  \<and> sym_refs (\<lambda>x. if x \<in> set q then {r \<in> state_refs_of s x. snd r = TCBBound}
                                  else state_refs_of s x)
                  \<and> sym_refs (\<lambda>x. state_hyp_refs_of s x)
                  \<and> (\<forall>x\<in>set q. st_tcb_at (Not \<circ> (halted or awaiting_reply)) x s))\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. invs\<rbrace>"
sorry
(*  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule mapM_x_inv_wp2)
   apply (clarsimp simp: )
  apply wp
   apply (simp add:bound_refs_of_tcb_trans)
  apply wp[1]
          apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift
                                    valid_irq_node_typ sts_only_idle)
           apply (rule sts_st_tcb_at_cases, simp)
          apply (strengthen reply_cap_doesnt_exist_strg)
          apply (auto simp: valid_tcb_state_def idle_no_ex_cap o_def if_split_asm
                     elim!: rsubst[where P=sym_refs] st_tcb_weakenE
                    intro!: ext)
  done*)


lemma ep_no_bound_refs:
  "ep_at p s \<Longrightarrow> {r \<in> state_refs_of s p. snd r = TCBBound} = {}"
  by (clarsimp simp: obj_at_def state_refs_of_def refs_of_def is_ep ep_q_refs_of_def split: endpoint.splits)

lemma obj_at_conj_distrib:
  "obj_at (\<lambda>ko. P ko \<and> Q ko) p s \<Longrightarrow> obj_at (\<lambda>ko. P ko) p s \<and> obj_at (\<lambda>ko. Q ko) p s"
  by (auto simp:obj_at_def)

lemma ep_q_refs_of_no_ntfn_bound:
  "(x, tp) \<in> ep_q_refs_of ep \<Longrightarrow> tp \<noteq> NTFNBound"
  by (auto simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ep_q_refs_of ep"
  by (clarsimp simp: ep_q_refs_of_def split:endpoint.splits)

lemma ep_list_tcb_at:
  "\<lbrakk>ep_at p s; valid_objs s; state_refs_of s p = set q \<times> {k}; x \<in> set q \<rbrakk> \<Longrightarrow> tcb_at x s"
  apply (erule (1) obj_at_valid_objsE)
  apply (fastforce simp:is_ep valid_obj_def valid_ep_def state_refs_of_def split:endpoint.splits)
  done

lemma tcb_at_no_ntfn_bound:
  "\<lbrakk> valid_objs s; tcb_at x s \<rbrakk> \<Longrightarrow> (t, NTFNBound) \<notin> state_refs_of s x"
  by (auto elim!: obj_at_valid_objsE
           simp: state_refs_of_def is_tcb valid_obj_def get_refs_def tcb_st_refs_of_def
           split:thread_state.splits option.splits if_splits)

lemma ep_no_ntfn_bound:
  "\<lbrakk>is_ep ko; refs_of ko = set q \<times> {NTFNBound}; y \<in> set q \<rbrakk> \<Longrightarrow> False"
  apply (subst (asm) set_eq_iff)
  apply (drule_tac x="(y, NTFNBound)" in spec)
  apply (clarsimp simp: refs_of_rev is_ep)
  done

lemma cancel_all_ipc_invs_helper:
  assumes x: "\<And>x ko. (x, symreftype k) \<in> refs_of ko
                \<Longrightarrow> (refs_of ko = {(x, symreftype k)} \<or>
                          (\<exists>y. refs_of ko = {(x, symreftype k), (y, TCBBound)}))"
  shows
  "\<lbrace>invs and obj_at (\<lambda>ko. is_ep ko \<and> refs_of ko = set q \<times> {k}) p\<rbrace>
     do y \<leftarrow> set_endpoint p Structures_A.endpoint.IdleEP;
        y \<leftarrow> mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                           do_extended_op (tcb_sched_action (tcb_sched_enqueue) t) od) q;
        do_extended_op reschedule_required
    od \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (subst bind_assoc[symmetric])
  apply (rule hoare_seq_ext)
   apply wp
   apply simp
  apply (rule hoare_pre)
   apply (wp cancel_all_invs_helper hoare_vcg_const_Ball_lift valid_irq_node_typ)
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_ep_def live_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule(1) sym_refs_obj_atD, clarsimp)
   apply (drule(1) bspec, erule(1) if_live_then_nonz_capD)
   apply (rule refs_of_live, clarsimp)
  apply (rule conjI[rotated])
   apply (subgoal_tac "\<exists>ep. ko_at (Endpoint ep) p s", clarsimp)
  apply (subgoal_tac "\<exists>rt. (x, rt) \<in> ep_q_refs_of ep", clarsimp)
     apply (fastforce elim!: ep_queued_st_tcb_at)
    apply (clarsimp simp: obj_at_def is_ep_def)+
   apply (case_tac ko, simp_all)
  apply (frule(1) sym_refs_obj_atD)
  apply (frule obj_at_state_refs_ofD)
  apply (clarsimp dest!:obj_at_conj_distrib)
  apply (thin_tac "obj_at (\<lambda>ko. refs_of ko = set q \<times> {k}) p s")
  apply (erule delta_sym_refs)
   apply (clarsimp simp: if_split_asm)+
  apply (safe)
          apply (fastforce dest!:symreftype_inverse' ep_no_ntfn_bound)
         apply (clarsimp dest!: symreftype_inverse')
         apply (frule (3) ep_list_tcb_at)
         apply (frule_tac t=y in tcb_at_no_ntfn_bound, simp+)
       apply (clarsimp dest!: symreftype_inverse')
       apply (frule (3) ep_list_tcb_at)
       apply (clarsimp simp: obj_at_def is_tcb is_ep)
      apply (fastforce dest!: obj_at_state_refs_ofD x)
     apply (fastforce dest!: obj_at_state_refs_ofD x)
    apply (fastforce dest!: symreftype_inverse' ep_no_ntfn_bound)
   apply (clarsimp)
  apply (fastforce dest!: symreftype_inverse' ep_no_ntfn_bound)
  done

lemma cancel_all_ipc_invs:
  "\<lbrace>invs\<rbrace> cancel_all_ipc epptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: get_ep_queue_def)
    apply (wp, fastforce)
(*   apply (rule hoare_pre, rule cancel_all_ipc_invs_helper[where k=EPSend])
    apply (fastforce simp: refs_of_rev get_refs_def split: option.splits)
   apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  apply (rule hoare_pre, rule cancel_all_ipc_invs_helper[where k=EPRecv])
   apply (fastforce simp: refs_of_rev tcb_bound_refs_def split: option.splits)
  apply (clarsimp elim!: obj_at_weakenE simp: is_ep)
  done*) sorry

lemma ntfn_q_refs_no_NTFNBound:
  "(x, NTFNBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)

lemma ntfn_q_refs_no_TCBBound:
  "(x, TCBBound) \<notin> ntfn_q_refs_of ntfn"
  by (auto simp: ntfn_q_refs_of_def split:ntfn.splits)
(*
lemma ntfn_bound_tcb_get_set[simp]:
  "ntfn_bound_tcb (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn ntfn') = ntfn'"
  by auto

lemma ntfn_obj_tcb_get_set[simp]:
  "ntfn_obj (ntfn_set_bound_tcb ntfn ntfn') = ntfn_obj ntfn"
  by auto

lemma valid_ntfn_set_bound_None:
  "valid_ntfn ntfn s \<Longrightarrow> valid_ntfn (set_ntfn_obj_ref ntfn_bound_tcb_update ntfn None) s"
  by (auto simp: valid_ntfn_def split:ntfn.splits)
*)
lemma ntfn_bound_tcb_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    ntfn_bound_tcb ntfn = Some tcbptr; P (Some ntfnptr)\<rbrakk>
  \<Longrightarrow> bound_tcb_at P tcbptr s"
  apply (drule_tac x=ntfnptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps
             elim!: valid_objsE)
  done

lemma bound_tcb_bound_notification_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s ntfnptr = Some (Notification ntfn);
    bound_tcb_at (\<lambda>ptr. ptr = (Some ntfnptr)) tcbptr s \<rbrakk>
  \<Longrightarrow> ntfn_bound_tcb ntfn = Some tcbptr"
  apply (drule_tac x=tcbptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def pred_tcb_at_def obj_at_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_ntfn_def is_tcb
                    state_refs_of_def refs_of_rev
          simp del: refs_of_simps
             elim!: valid_objsE)
  done

lemma set_tcb_obj_ref_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> set_tcb_obj_ref f t new \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def get_tcb_def
                split: option.splits kernel_object.splits)
  sorry

lemma unbind_notification_invs:
  notes hoare_pre [wp_pre del]
  shows "\<lbrace>invs\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unbind_notification_def invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ gbn_sp])
  apply (case_tac ntfnptr, clarsimp, wpsimp wp: maybeM_inv)
(*  apply clarsimp
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (wp valid_irq_node_typ set_simple_ko_valid_objs
       | clarsimp)+
          defer 5
          apply (auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                       simp: live_def valid_ntfn_set_bound_None is_ntfn valid_obj_def)[9]
  apply (clarsimp simp: if_split)
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def is_tcb
                   dest!: pred_tcb_at_tcb_at ko_at_state_refs_ofD
                   split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (frule pred_tcb_at_tcb_at)
   apply (frule_tac p=t in obj_at_ko_at, clarsimp)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (fastforce simp: obj_at_def is_tcb ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound refs_of_rev
                          tcb_ntfn_is_bound_def
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  apply (fastforce simp: ntfn_bound_refs_def obj_at_def ntfn_q_refs_no_TCBBound
                  elim!: pred_tcb_weakenE
                  dest!: bound_tcb_bound_notification_at refs_in_ntfn_bound_refs symreftype_inverse'
                  split: option.splits)
  done*) sorry

lemma cancel_all_signals_bound_tcb_at[wp]:
  "\<lbrace>bound_tcb_at P t\<rbrace> cancel_all_signals param_a \<lbrace>\<lambda>_. bound_tcb_at P t\<rbrace>"
  by (wpsimp simp: cancel_all_signals_def get_simple_ko_def get_object_def wp: mapM_x_wp_inv)

lemma waiting_ntfn_list_tcb_at:
  "\<lbrakk>valid_objs s; ko_at (Notification ntfn) ntfnptr s; ntfn_obj ntfn = WaitingNtfn x\<rbrakk> \<Longrightarrow> \<forall>t \<in> set x. tcb_at t s"
  by (fastforce elim!: obj_at_valid_objsE simp:valid_obj_def valid_ntfn_def)

lemma tcb_at_ko_at:
  "tcb_at p s \<Longrightarrow> \<exists>tcb. ko_at (TCB tcb) p s"
  by (fastforce simp: obj_at_def is_tcb)

lemma tcb_state_refs_no_tcb:
  "\<lbrakk>valid_objs s; tcb_at y s; (x, ref) \<in> state_refs_of s y\<rbrakk> \<Longrightarrow> ~ tcb_at x s"
  apply (clarsimp simp: ko_at_state_refs_ofD dest!: tcb_at_ko_at)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: is_tcb valid_obj_def)
  apply (erule disjE)
   apply (clarsimp simp: tcb_st_refs_of_def valid_tcb_def valid_tcb_state_def obj_at_def
                         is_ep is_ntfn is_tcb
                  split:thread_state.splits)
  apply (clarsimp simp: get_refs_def valid_tcb_def obj_at_def is_ntfn
                  split:option.splits)
  sorry

lemma cancel_all_signals_invs:
  "\<lbrace>invs\<rbrace> cancel_all_signals ntfnptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp cancel_all_invs_helper set_simple_ko_valid_objs valid_irq_node_typ
             hoare_vcg_const_Ball_lift
        | wpc
        | simp add: live_def)+
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
(*  apply (rule conjI)
   apply (fastforce simp: valid_obj_def valid_ntfn_def elim!: obj_at_valid_objsE)
  apply (rule conjI)
   apply (fastforce simp: live_def elim!: if_live_then_nonz_capD)
  apply (rule conjI)
   apply (fastforce simp: is_ntfn elim!: ko_at_weakenE)
  apply (rule conjI)
  apply (fastforce simp: st_tcb_at_refs_of_rev
                    dest: bspec sym_refs_ko_atD
                    elim: st_tcb_ex_cap)
  apply (rule conjI[rotated])
   apply (fastforce elim!: ntfn_queued_st_tcb_at)

  apply (rule delta_sym_refs, assumption)
   apply (fastforce dest!: refs_in_ntfn_bound_refs ko_at_state_refs_ofD
                    split: if_split_asm)
  apply (clarsimp split:if_split_asm)
    apply (fastforce dest: waiting_ntfn_list_tcb_at refs_in_ntfn_bound_refs
                     simp: obj_at_def is_tcb_def)
   apply (rule conjI)
    apply (fastforce dest: refs_in_ntfn_bound_refs symreftype_inverse')
   apply (frule (2) waiting_ntfn_list_tcb_at)
   apply (fastforce simp: st_tcb_at_refs_of_rev refs_in_tcb_bound_refs
                    dest: bspec sym_refs_ko_atD st_tcb_at_state_refs_ofD)
  apply (fastforce simp: ntfn_bound_refs_def valid_obj_def valid_ntfn_def refs_of_rev
                  dest!: symreftype_inverse' ko_at_state_refs_ofD
                  split: option.splits
                  elim!: obj_at_valid_objsE)
  done*) sorry

lemma cancel_all_unlive_helper:
  "\<lbrace>obj_at (\<lambda>obj. \<not> live obj \<and> (\<forall>tcb. obj \<noteq> TCB tcb)) ptr\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule hoare_strengthen_post [OF mapM_x_wp'])
   apply (simp add: set_thread_state_def set_object_def)
   apply (wp | simp only: obj_at_exst_update)+
   apply (clarsimp dest!: get_tcb_SomeD)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp elim!: obj_at_weakenE)
  done


lemma cancel_all_ipc_unlive[wp]:
  "\<lbrace>\<top>\<rbrace> cancel_all_ipc ptr \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all add: set_simple_ko_def get_ep_queue_def)
    apply wp
    apply (clarsimp simp: live_def elim!: obj_at_weakenE)
   apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
   apply (clarsimp simp: live_def)
(*  apply (wp cancel_all_unlive_helper set_object_at_obj3 | simp only: obj_at_exst_update)+
  apply (clarsimp simp: live_def)
  done*) sorry


(* This lemma should be sufficient provided that each notification object is unbound BEFORE the 'cancel_all_signals' function is invoked. TODO: Check the abstract specification and the C and Haskell implementations that this is indeed the case. *)
lemma cancel_all_signals_unlive[wp]:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None) ntfnptr s\<rbrace>
     cancel_all_signals ntfnptr
   \<lbrace>\<lambda> rv. obj_at (Not \<circ> live) ntfnptr\<rbrace>"
  apply (simp add: cancel_all_signals_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wp
        | wpc
        | simp add: unbind_maybe_notification_def)+
     apply (rule_tac Q="\<lambda>_. obj_at (is_ntfn and Not \<circ> live) ntfnptr" in hoare_post_imp)
      apply (fastforce elim: obj_at_weakenE)
     apply (wp mapM_x_wp' sts_obj_at_impossible
          | simp add: is_ntfn)+
(*  apply (simp add: set_simple_ko_def)
    apply (wp get_object_wp obj_set_prop_at)
  apply (auto simp: live_def pred_tcb_at_def obj_at_def)
  done*) sorry


crunch cte_wp_at[wp]: cancel_all_ipc "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp)

crunch cte_wp_at[wp]: cancel_all_signals "cte_wp_at P p"
  (wp: crunch_wps mapM_x_wp thread_set_cte_wp_at_trivial
   simp: tcb_cap_cases_def)

lemma cancel_badged_sends_filterM_helper':
  "\<forall>ys.
   \<lbrace>\<lambda>s. all_invs_but_sym_refs s  \<and> sym_refs (state_hyp_refs_of s) \<and> distinct (xs @ ys) \<and> ep_at epptr s
           \<and> ex_nonz_cap_to epptr s
           \<and> sym_refs ((state_refs_of s) (epptr := ((set (xs @ ys)) \<times> {EPSend})))
           \<and> (\<forall>x \<in> set (xs @ ys). {r \<in> state_refs_of s x. snd r \<noteq> TCBBound} = {(epptr, TCBBlockedSend)})\<rbrace>
      filterM (\<lambda>t. do st \<leftarrow> get_thread_state t;
                      if blocking_ipc_badge st = badge
                      then do y \<leftarrow> set_thread_state t Structures_A.thread_state.Restart;
                              y \<leftarrow> do_extended_op (tcb_sched_action action t);
                              return False
                      od
                      else return True
                   od) xs
   \<lbrace>\<lambda>rv s. all_invs_but_sym_refs s \<and> sym_refs (state_hyp_refs_of s)
            \<and> ep_at epptr s \<and> (\<forall>x \<in> set (xs @ ys). tcb_at x s)
            \<and> ex_nonz_cap_to epptr s
            \<and> (\<forall>y \<in> set ys. {r \<in> state_refs_of s y. snd r \<noteq> TCBBound} = {(epptr, TCBBlockedSend)})
            \<and> distinct rv \<and> distinct (xs @ ys) \<and> (set rv \<subseteq> set xs)
            \<and> sym_refs ((state_refs_of s) (epptr := ((set rv \<union> set ys) \<times> {EPSend})))\<rbrace>"
  apply (rule rev_induct[where xs=xs])
   apply (rule allI, simp)
   apply wp
   apply clarsimp
   apply (drule(1) bspec, drule singleton_eqD, clarsimp, drule state_refs_of_elemD)
   apply (clarsimp simp: st_tcb_at_refs_of_rev pred_tcb_at_def is_tcb
                  elim!: obj_at_weakenE)
  apply (clarsimp simp: filterM_append bind_assoc simp del: set_append distinct_append)
  apply (drule spec, erule hoare_seq_ext[rotated])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (rule hoare_pre,
         wpsimp wp: valid_irq_node_typ sts_only_idle hoare_vcg_const_Ball_lift)
  apply (clarsimp simp: valid_tcb_state_def)
  apply (rule conjI[rotated])
   apply blast
  apply clarsimp
  apply (thin_tac "obj_at f epptr s" for f s)
  apply (thin_tac "tcb_at x s" for x s)
  apply (thin_tac "sym_refs (state_hyp_refs_of s)" for s)
  apply (frule singleton_eqD, clarify, drule state_refs_of_elemD)
  apply (frule(1) if_live_then_nonz_capD)
  apply (rule refs_of_live, clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev)
  apply (clarsimp simp: pred_tcb_def2 valid_idle_def)
  apply (rule conjI, clarsimp)
  apply (rule conjI, clarsimp)
  apply force
  apply (erule delta_sym_refs)
   apply (simp split: if_split_asm)
  apply (simp split: if_split_asm)
   apply fastforce
  apply (subgoal_tac "(y, tp) \<in> {r \<in> state_refs_of s x. snd r \<noteq> TCBBound}")
   apply clarsimp
   apply fastforce
  apply fastforce
  done

lemmas cancel_badged_sends_filterM_helper
    = spec [where x=Nil, OF cancel_badged_sends_filterM_helper', simplified]

lemma cancel_badged_sends_invs_helper:
  "{r. snd r \<noteq> TCBBound \<and>
       (r \<in> tcb_st_refs_of ts \<or> r \<in> get_refs TCBBound ntfnptr)} =
   tcb_st_refs_of ts"
  by (auto simp add: tcb_st_refs_of_def get_refs_def split: thread_state.splits option.splits)

lemma cancel_badged_sends_invs[wp]:
  "\<lbrace>invs\<rbrace> cancel_badged_sends epptr badge \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cancel_badged_sends_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac ep; simp)
    apply wpsimp
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wpsimp wp: valid_irq_node_typ)
     apply (simp add: fun_upd_def[symmetric] ep_redux_simps ep_at_def2[symmetric, simplified]
                cong: list.case_cong)
(*     apply (rule hoare_strengthen_post,
            rule cancel_badged_sends_filterM_helper[where epptr=epptr])
     apply (auto intro:obj_at_weakenE)[1]
    apply (wpsimp wp: valid_irq_node_typ set_endpoint_ep_at)
   apply (clarsimp simp: valid_ep_def conj_comms)
   apply (subst obj_at_weakenE, simp, fastforce)
    apply (clarsimp simp: is_ep_def)
   apply (frule(1) sym_refs_ko_atD, clarsimp)
   apply (frule(1) if_live_then_nonz_capD, (clarsimp simp: live_def)+)
   apply (erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ep_def st_tcb_at_refs_of_rev)
   apply (simp add: fun_upd_idem obj_at_def is_ep_def | subst fun_upd_def[symmetric])+
   apply (clarsimp, drule(1) bspec)
   apply (drule st_tcb_at_state_refs_ofD)
   apply (clarsimp simp only: cancel_badged_sends_invs_helper Un_iff, clarsimp)
   apply (simp add: set_eq_subset)
  apply wpsimp
  done*) sorry


lemma real_cte_emptyable_strg:
  "real_cte_at p s \<longrightarrow> emptyable p s"
  by (clarsimp simp: emptyable_def obj_at_def is_tcb is_cap_table)

end
