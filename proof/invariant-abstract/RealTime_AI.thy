(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory RealTime_AI
imports VSpace_AI
begin

lemma maybeM_inv[wp]:
  "\<forall>a. \<lbrace>P\<rbrace> f a \<lbrace>\<lambda>_. P\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> maybeM f opt \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: maybeM_def; fastforce)

text {* update\_sched\_context *}


lemma update_sched_context_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> update_sched_context p pd \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done

lemma update_sched_context_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> update_sched_context p pd \<lbrace>\<lambda>_. cte_wp_at P c\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases)
  done

lemma update_sched_context_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  sorry

lemma update_sched_context_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_pspace_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_mdb[wp]:
  "\<lbrace>valid_mdb\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_if_unsafe_then_cap[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. if_unsafe_then_cap\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_if_live_then_nonz_cap[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  sorry

lemma update_sched_context_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  sorry

lemma update_sched_context_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at  P t\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_ . st_tcb_at  P t\<rbrace>"
  sorry

lemma update_sched_context_valid_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_global_objs[wp]:
  "\<lbrace>valid_global_objs\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_global_vspace_mappings\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_equal_kernel_mappings[wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. pspace_in_kernel_window\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma update_sched_context_valid_machine_state[wp]:
  "\<lbrace>valid_machine_state\<rbrace> update_sched_context ref ref2 \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (wpsimp simp: update_sched_context_def get_object_def bind_assoc set_object_def)
 sorry

lemma refs_in_get_refs:
  "(x, ref) \<in> get_refs REF ntfn \<Longrightarrow> ref = REF"
  by (auto simp: get_refs_def split: option.splits)

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)

lemma reply_remove_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  sorry


crunch interrupt_states[wp]: set_sched_context "\<lambda>s. P (interrupt_states s)"
  (simp: get_object_def)

lemma reply_remove_interrupt_states[wp]: "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  sorry

lemma reply_remove_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> reply_remove r \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  sorry

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)

lemmas reply_remove_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF reply_remove_caps_of_state
                                  reply_remove_interrupt_states]

lemma reply_remove_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  sorry

lemma reply_remove_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  sorry

lemma reply_remove_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  sorry


lemma reply_remove_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  sorry

lemma reply_remove_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
   sorry

crunch arch [wp]: set_reply "\<lambda>s. P (arch_state s)"
  (simp: get_object_def)

lemma reply_remove_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  sorry


lemma reply_remove_valid_objs [wp]:
  "\<lbrace>valid_objs and reply_at r\<rbrace> reply_remove r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  sorry

lemma reply_remove_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  sorry

lemma reply_remove_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  sorry

lemma reply_remove_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> reply_remove r \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  sorry

lemma reply_remove_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> reply_remove r \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  sorry

lemma reply_remove_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> reply_remove r \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  sorry

lemma reply_remove_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> reply_remove r \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  sorry

lemma reply_remove_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> reply_remove r \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  sorry

lemma reply_remove_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_remove r \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma reply_remove_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  reply_remove r
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  sorry

lemma reply_remove_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  sorry

(*
lemma reply_remove_[wp]:
      "\<lbrace>\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<rbrace>"
*)
lemma set_sched_context_invs[wp]:
  "\<lbrace> invs and sc_at sc_ptr \<rbrace>
      update_sched_context sc_ptr sc \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def)
  sorry

lemma set_reply_invs[wp]:
  "\<lbrace> invs and reply_at rptr \<rbrace>
      set_reply rptr reply \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: set_simple_ko_def)
  sorry

lemma reply_unbind_tcb_invs:
  "\<lbrace> invs and sc_at sc_ptr and reply_at rptr \<rbrace>
      reply_unlink_tcb rptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_unlink_tcb_def)
  sorry

lemma reply_unbind_sc_invs:
  "\<lbrace> invs and sc_at sc_ptr and reply_at rptr \<rbrace>
      reply_unlink_sc sc_ptr rptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_unlink_sc_def)
  sorry

lemma sched_context_unbind_tcb_invs:
  "\<lbrace> invs and sc_at sc_ptr \<rbrace>
      sched_context_unbind_tcb sc_ptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: sched_context_unbind_tcb_def)
  sorry

lemma sched_context_donate_invs:
  "\<lbrace> invs and sc_at sc_ptr and tcb_at tptr \<rbrace>
      sched_context_donate sc_ptr tptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: sched_context_donate_def)
  sorry

lemma reply_unbind_caller_invs[wp]:
  "\<lbrace> invs and tcb_at tptr and reply_at rptr \<rbrace>
      reply_unbind_caller tptr tptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_unbind_caller_def)
  sorry

lemma reply_remove_invs:
  "\<lbrace> invs and reply_at r \<rbrace> reply_remove r \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_remove_def | wpc)+
  sorry


lemma reply_push_invs:
  "\<lbrace> invs and reply_at r and tcb_at caller and tcb_at callee\<rbrace>
      reply_push caller callee rptr b \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_push_def)
  sorry

(*
crunch typ_at[wp]: postpone, sched_context_bind_tcb "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (ignore: check_cap_at setNextPC zipWithM
       wp: hoare_drop_imps mapM_x_wp' maybeM_inv select_wp
     simp: crunch_simps)  (* RT FIXME: Move *)
*)
lemma sc_and_timer_empty_fail[wp]:
  "empty_fail sc_and_timer"
  sorry (* RT FIXME: Move *)

(* FIXME: move *)
lemma tcb_at_typ_at:
  "\<lbrace>typ_at ATCB t\<rbrace> f \<lbrace>\<lambda>_. typ_at ATCB t\<rbrace> \<Longrightarrow> \<lbrace>tcb_at t\<rbrace> f \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ)

lemma valid_bound_tcb_typ_at:
  "\<forall>p. \<lbrace>\<lambda>s. typ_at ATCB p s\<rbrace> f \<lbrace>\<lambda>_ s. typ_at ATCB p s\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>s. valid_bound_tcb tcb s\<rbrace> f \<lbrace>\<lambda>_ s. valid_bound_tcb tcb s\<rbrace>"
  apply (clarsimp simp: valid_bound_obj_def split: option.splits)
  apply (wpsimp wp: hoare_vcg_all_lift tcb_at_typ_at static_imp_wp)
  done

crunch typ_at[wp]: sched_context_donate, maybe_donate_sc, maybe_return_sc "\<lambda>(s::det_ext state). P (typ_at T t s)"
(wp: hoare_drop_imps maybeM_inv)  (* RT FIXME: Move *)

crunch bound_tcb[wp]: schedule_tcb "valid_bound_tcb t"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM) (* RT FIXME: Move *)

crunch typ_at[wp]: schedule_tcb "\<lambda>s. P (typ_at T p s)"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM) (* RT FIXME: Move *)

crunch cap_to[wp]: sched_context_donate, sort_queue, schedule_tcb, maybe_donate_sc, maybe_return_sc
 "ex_nonz_cap_to p:: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps maybeM_inv) (* RT FIXME: Move *)

lemma sched_context_unbind_tcb_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_unbind_tcb scref \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: hoare_drop_imp
           simp: sched_context_unbind_tcb_def)

lemma sched_context_unbind_all_tcbs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> sched_context_unbind_all_tcbs scref \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def)

crunch typ_at[wp]: sched_context_unbind_ntfn, sched_context_update_consumed "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv)

lemma sched_context_update_consumed_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> sched_context_update_consumed param_a \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace> "
sorry

crunch typ_at[wp]: get_sched_context, set_sched_context "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv simp: get_object_def)
crunch typ_at[wp]: sched_context_unbind_yield_from "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps ignore: get_ntfn_obj_ref)
crunch typ_at[wp]: unbind_from_sc, sched_context_maybe_unbind_ntfn, reply_unlink_sc, sched_context_clear_replies, sched_context_unbind_yield_from "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps ignore: get_ntfn_obj_ref)


end