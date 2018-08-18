(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTcb_AI
imports "../Tcb_AI"
begin

context Arch begin global_naming ARM

named_theorems Tcb_AI_asms


lemma activate_idle_invs[Tcb_AI_asms]:
  "\<lbrace>invs and ct_idle\<rbrace>
     arch_activate_idle_thread thread
   \<lbrace>\<lambda>rv. invs and ct_idle\<rbrace>"
  by (simp add: arch_activate_idle_thread_def)


lemma empty_fail_getRegister [intro!, simp, Tcb_AI_asms]:
  "empty_fail (getRegister r)"
  by (simp add: getRegister_def)


lemma same_object_also_valid:  (* arch specific *)
  "\<lbrakk> same_object_as cap cap'; s \<turnstile> cap'; wellformed_cap cap;
     cap_asid cap = None \<or> (\<exists>asid. cap_asid cap = Some asid \<and> 0 < asid \<and> asid \<le> 2^asid_bits - 1);
     cap_vptr cap = None; cap_asid_base cap = None \<rbrakk>
     \<Longrightarrow> s \<turnstile> cap"
  apply (cases cap,
         (clarsimp simp: same_object_as_def is_cap_simps cap_asid_def
                         wellformed_cap_def wellformed_acap_def
                         valid_cap_def bits_of_def cap_aligned_def
                   split: cap.split_asm arch_cap.split_asm option.splits)+)
  done

lemma same_object_obj_refs[Tcb_AI_asms]:
  "\<lbrakk> same_object_as cap cap' \<rbrakk>
     \<Longrightarrow> obj_refs cap = obj_refs cap'"
  apply (cases cap, simp_all add: same_object_as_def)
       apply ((clarsimp simp: is_cap_simps bits_of_def
                      split: cap.split_asm )+)
  by (cases "the_arch_cap cap"; cases "the_arch_cap cap'"; simp)


definition
  is_cnode_or_valid_arch :: "cap \<Rightarrow> bool"
where
 "is_cnode_or_valid_arch cap \<equiv>
    is_cnode_cap cap
     \<or> (is_arch_cap cap
          \<and> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
          \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None))"


definition (* arch specific *)
  "pt_pd_asid cap \<equiv> case cap of
    ArchObjectCap (PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | ArchObjectCap (PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

lemmas pt_pd_asid_simps [simp] = (* arch specific *)
  pt_pd_asid_def [split_simps cap.split arch_cap.split option.split prod.split]

lemma checked_insert_is_derived: (* arch specific *)
  "\<lbrakk> same_object_as new_cap old_cap; is_cnode_or_valid_arch new_cap;
     obj_refs new_cap = obj_refs old_cap
         \<longrightarrow> table_cap_ref old_cap = table_cap_ref new_cap
            \<and> pt_pd_asid old_cap = pt_pd_asid new_cap\<rbrakk>
     \<Longrightarrow> is_derived m slot new_cap old_cap"
  apply (cases slot)
  apply (frule same_object_as_cap_master)
  apply (frule master_cap_obj_refs)
  apply (frule cap_master_eq_badge_none)
  apply (frule same_master_cap_same_types)
  apply (simp add: is_derived_def)
  apply clarsimp
  apply (auto simp: is_cap_simps cap_master_cap_def
                    is_cnode_or_valid_arch_def vs_cap_ref_def
                    table_cap_ref_def pt_pd_asid_def up_ucast_inj_eq
             split: cap.split_asm arch_cap.split_asm
                    option.split_asm)[1]
  done

lemma is_cnode_or_valid_arch_cap_asid: (* arch specific *)
  "is_cnode_or_valid_arch cap
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> cap_asid cap \<noteq> None)
             \<and> (is_pd_cap cap \<longrightarrow> cap_asid cap \<noteq> None)"
  by (auto simp add: is_cnode_or_valid_arch_def
                     is_cap_simps)

lemma checked_insert_tcb_invs[wp]: (* arch specific *)
  "\<lbrace>invs and cte_wp_at (\<lambda>c. c = cap.NullCap) (target, ref)
        and K (is_cnode_or_valid_arch new_cap) and valid_cap new_cap
        and tcb_cap_valid new_cap (target, ref)
        and K (is_pt_cap new_cap \<or> is_pd_cap new_cap
                         \<longrightarrow> cap_asid new_cap \<noteq> None)
        and (cte_wp_at (\<lambda>c. obj_refs c = obj_refs new_cap
                              \<longrightarrow> table_cap_ref c = table_cap_ref new_cap \<and>
                                 pt_pd_asid c = pt_pd_asid new_cap) src_slot)\<rbrace>
     check_cap_at new_cap src_slot
      (check_cap_at (cap.ThreadCap target) slot
       (cap_insert new_cap src_slot (target, ref))) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: check_cap_at_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap[where p=src_slot], fastforce)
  apply (frule caps_of_state_valid_cap[where p=slot], fastforce)
  apply (rule conjI, simp only: ex_cte_cap_wp_to_def)
   apply (rule_tac x=slot in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state same_object_as_cte_refs)
   apply (clarsimp simp: same_object_as_def2 cap_master_cap_simps
                  dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: valid_cap_def[where c="cap.ThreadCap x" for x])
   apply (erule cte_wp_atE[OF caps_of_state_cteD])
    apply (fastforce simp: obj_at_def is_obj_defs)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (subgoal_tac "\<not> is_zombie new_cap")
    apply (simp add: same_object_zombies same_object_obj_refs)
    apply (erule(2) zombies_final_helperE)
      apply fastforce
     apply (fastforce simp add: cte_wp_at_caps_of_state)
    apply assumption
   apply (clarsimp simp: is_cnode_or_valid_arch_def is_cap_simps
                         is_valid_vtable_root_def)
  apply (rule conjI)
   apply (erule(1) checked_insert_is_derived, simp+)
  apply (auto simp: is_cnode_or_valid_arch_def is_cap_simps)
  done

crunch tcb_at[wp, Tcb_AI_asms]: arch_get_sanitise_register_info, arch_post_modify_registers "tcb_at a"
crunch invs[wp, Tcb_AI_asms]: arch_get_sanitise_register_info, arch_post_modify_registers "invs"
crunch ex_nonz_cap_to[wp, Tcb_AI_asms]: arch_get_sanitise_register_info, arch_post_modify_registers "ex_nonz_cap_to a"

lemma finalise_cap_not_cte_wp_at[Tcb_AI_asms]:
  assumes x: "P cap.NullCap"
  shows      "\<lbrace>\<lambda>s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>
                finalise_cap cap fin
              \<lbrace>\<lambda>rv s. \<forall>cp \<in> ran (caps_of_state s). P cp\<rbrace>"
  apply (cases cap, simp_all)
       apply (wp suspend_caps_of_state hoare_vcg_all_lift get_simple_ko_wp
            | simp
            | rule impI
            | rule hoare_drop_imps)+
     apply (clarsimp simp: ball_ran_eq x)
    apply (wp delete_one_caps_of_state
         | rule impI
         | simp add: deleting_irq_handler_def get_irq_slot_def x ball_ran_eq)+
    done


lemma table_cap_ref_max_free_index_upd[simp,Tcb_AI_asms]:
  "table_cap_ref (max_free_index_update cap) = table_cap_ref cap"
  by (simp add: free_index_update_def table_cap_ref_def split: cap.splits)


interpretation Tcb_AI_1? : Tcb_AI_1
  where is_cnode_or_valid_arch = is_cnode_or_valid_arch
  by (unfold_locales; fact Tcb_AI_asms)


lemma use_no_cap_to_obj_asid_strg: (* arch specific *)
  "(cte_at p s \<and> no_cap_to_obj_dr_emp cap s \<and> valid_cap cap s \<and> invs s)
         \<longrightarrow> cte_wp_at (\<lambda>c. obj_refs c = obj_refs cap
                \<longrightarrow> table_cap_ref c = table_cap_ref cap \<and> pt_pd_asid c = pt_pd_asid cap) p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state
                     no_cap_to_obj_with_diff_ref_def
           simp del: split_paired_All)
  apply (frule caps_of_state_valid_cap, fastforce)
  apply (erule allE)+
  apply (erule (1) impE)+
  apply (simp add: table_cap_ref_def pt_pd_asid_def split: cap.splits arch_cap.splits option.splits prod.splits)
  apply (fastforce simp: table_cap_ref_def valid_cap_simps elim!: asid_low_high_bits)+
  done

lemma cap_delete_no_cap_to_obj_asid[wp, Tcb_AI_asms]:
  "\<lbrace>no_cap_to_obj_dr_emp cap\<rbrace>
     cap_delete slot
   \<lbrace>\<lambda>rv. no_cap_to_obj_dr_emp cap\<rbrace>"
  apply (simp add: cap_delete_def
                   no_cap_to_obj_with_diff_ref_ran_caps_form)
  apply wp
  apply simp
  apply (rule use_spec)
  apply (rule rec_del_all_caps_in_range)
     apply (simp add: table_cap_ref_def[simplified, split_simps cap.split]
              | rule obj_ref_none_no_asid)+
  done

lemma as_user_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> as_user a b \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)

lemma as_user_ipc_tcb_cap_valid4[wp]:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap (t, tcb_cnode_index 2) s\<rbrace>
    as_user a b
   \<lbrace>\<lambda>rv. tcb_cap_valid cap (t, tcb_cnode_index 2)\<rbrace>"
  apply (simp add: as_user_def set_object_def)
  apply (wp | wpc | simp)+
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def is_tcb
                 dest!: get_tcb_SomeD)
  apply (clarsimp simp: get_tcb_def)
  done

lemma tcb_cap_valid_ep_strgs:
  "is_ep_cap cap \<or> NullCap = cap \<longrightarrow> tcb_cap_valid cap (t, tcb_cnode_index 3) s"
  "is_ep_cap cap \<or> NullCap = cap \<longrightarrow> tcb_cap_valid cap (t, tcb_cnode_index 4) s"
  by (auto simp: tcb_cap_valid_def st_tcb_at_def obj_at_def is_tcb)

lemma sched_context_unbind_tcb_valid_cap[wp]:
  "sched_context_unbind_tcb t \<lbrace>valid_cap c\<rbrace>"
  by (rule abs_typ_at_lifts) wp

lemma sched_context_bind_tcb_valid_cap[wp]:
  "sched_context_bind_tcb t s \<lbrace>valid_cap c\<rbrace>"
  by (rule abs_typ_at_lifts) wp

lemma sched_context_bind_tcb_cte_wp_at[wp]:
  "sched_context_bind_tcb t s \<lbrace>cte_wp_at P p\<rbrace>"
  unfolding sched_context_bind_tcb_def by wpsimp

lemma sched_context_bind_tcb_caps_of_state[wp]:
  "sched_context_bind_tcb t s \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding sched_context_bind_tcb_def by wpsimp

lemma sched_context_unbind_tcb_no_cap_to_obj_ref[wp]:
  "sched_context_unbind_tcb t \<lbrace>no_cap_to_obj_with_diff_ref c S\<rbrace>"
  by (rule no_cap_to_obj_with_diff_ref_lift) wpsimp

lemma sched_context_bind_tcb_no_cap_to_obj_ref[wp]:
  "sched_context_bind_tcb t s \<lbrace>no_cap_to_obj_with_diff_ref c S\<rbrace>"
  by (rule no_cap_to_obj_with_diff_ref_lift) wpsimp

lemma sort_queue_valid_ntfn_rv:
  "\<lbrace>valid_ntfn ntfn and K (ntfn_obj ntfn = WaitingNtfn q)\<rbrace>
    sort_queue q
   \<lbrace>\<lambda>rv. valid_ntfn (ntfn\<lparr>ntfn_obj := WaitingNtfn rv\<rparr>)\<rbrace>"
  apply (clarsimp simp: valid_def sort_queue_def bind_def return_def)
  apply (case_tac q; clarsimp simp: valid_ntfn_def split: option.splits)
   apply (case_tac a, clarsimp simp: in_monad mapM_Cons)
   apply (clarsimp simp del: sort_key_simps(2) zip_Cons_Cons)
   apply (rule conjI, clarsimp)
  sorry

lemma reorder_ntfn_invs[wp]:
  "\<lbrace>invs\<rbrace> reorder_ntfn ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: reorder_ntfn_def live_def live_ntfn_def
                  wp: set_ntfn_minor_invs sort_queue_valid_ntfn_rv get_simple_ko_wp)
  apply (clarsimp simp: ntfn_queue_def split: ntfn.splits)
  apply (rule conjI, clarsimp simp: obj_at_def)
  apply (rule obj_at_valid_objsE, assumption, fastforce)
  apply (frule if_live_then_nonz_capD[OF invs_iflive], assumption)
   by (auto dest!: not_idle_tcb_in_waitingntfn
             simp: valid_obj_def live_def live_ntfn_def)


lemma set_ep_minor_invs:
  "\<lbrace>invs and obj_at (\<lambda>ko. refs_of ko = ep_q_refs_of val) ptr
         and valid_ep val
         and (\<lambda>s. \<forall>typ. (idle_thread s, typ) \<notin> ep_q_refs_of val)
         and (\<lambda>s. live (Endpoint val) \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     set_endpoint ptr val
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
          wp: valid_irq_node_typ simp_del: fun_upd_apply)
  apply (clarsimp simp: state_refs_of_def obj_at_def ext elim!: rsubst[where P = sym_refs])
  done

lemma reorder_ep_invs[wp]:
  "\<lbrace>invs\<rbrace> reorder_ep ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: reorder_ep_def live_def
                  wp: set_ep_minor_invs sort_queue_valid_ntfn_rv get_simple_ko_wp)
  sorry


crunch invs[wp]: thread_set_priority invs

lemma set_priority_invs[wp]:
  "\<lbrace>invs\<rbrace> set_priority a prio \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: set_priority_def reorder_ntfn_def)
  apply wpsimp
  done

crunch caps_of_state[wp]: set_priority "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps maybeM_inv simp: crunch_simps)

crunches set_priority
  for typ_at[wp]:  "\<lambda>s. P (typ_at T p s)"
  and no_cap_to[wp]: "no_cap_to_obj_with_diff_ref a S"
  (wp: crunch_wps no_cap_to_obj_with_diff_ref_lift maybeM_inv simp: crunch_simps ignore: set_object)

lemma sc_tcb_sc_at_ready_queues_update[simp]:
  "sc_tcb_sc_at P t s \<Longrightarrow> sc_tcb_sc_at P t (ready_queues_update f s)"
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma sc_tcb_sc_at_sch_act_update[simp]:
  "sc_tcb_sc_at P t s \<Longrightarrow> sc_tcb_sc_at P t (scheduler_action_update f s)"
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)

lemma sc_tcb_sc_at_ekh_act_update[simp]:
  "sc_tcb_sc_at P t s \<Longrightarrow> sc_tcb_sc_at P t (ekheap_update f s)"
  by (clarsimp simp: sc_tcb_sc_at_def obj_at_def)


(* FIXME move: KHeap_AI *)
lemma set_notification_obj_at_impossible:
  "\<forall>ep. \<not> (P (Notification ep)) \<Longrightarrow>
    \<lbrace>\<lambda>s. Q (obj_at P p s)\<rbrace> set_notification ptr endp \<lbrace>\<lambda>rv s. Q (obj_at P p s)\<rbrace>"
  apply (simp add: set_simple_ko_def set_object_def cong: kernel_object.case_cong)
  apply (wpsimp wp: get_object_wp set_object_at_obj)
  apply (clarsimp simp: obj_at_def split: option.splits)
  done

lemma reorder_ntfn_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P t\<rbrace> reorder_ntfn a \<lbrace>\<lambda>rv. sc_tcb_sc_at P t\<rbrace>"
  by (wpsimp simp: reorder_ntfn_def sc_tcb_sc_at_def
                  wp: set_notification_obj_at_impossible get_simple_ko_wp)

lemma reorder_ep_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P t\<rbrace> reorder_ep a \<lbrace>\<lambda>rv. sc_tcb_sc_at P t\<rbrace>"
  by (wpsimp simp: reorder_ep_def sc_tcb_sc_at_def
                  wp: set_endpoint_obj_at_impossible get_simple_ko_wp)

crunches tcb_sched_action, reschedule_required
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  and sc_tcb_sc_at[wp]: "sc_tcb_sc_at P t"

crunches set_priority
  for valid_cap[wp]: "valid_cap cap"
  and no_cap_to_diff_ref[wp]: "no_cap_to_obj_with_diff_ref a S"
  and cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  and pred_tcb_at[wp]: "pred_tcb_at proj P t"
  and sc_tcb_sc_at[wp]: "sc_tcb_sc_at P t"
  (wp: valid_cap_typ crunch_wps maybeM_inv no_cap_to_obj_with_diff_ref_lift reschedule_required_pred_tcb_at
   simp: crunch_simps cte_wp_at_caps_of_state)

lemma fold_is_tcb_obj_at[simp]:
  "obj_at (\<lambda>ko. \<exists>t. ko = TCB t) p s = tcb_at p s"
  by (clarsimp simp: is_tcb obj_at_def)

lemma horridly_specific_rewrite:
  "(obj_at (\<lambda>ko. \<exists>tcb. (tcb_sched_context tcb = Some xa \<longrightarrow> ko = TCB tcb) \<and>
                   (tcb_sched_context tcb \<noteq> Some xa \<longrightarrow>
                        ex_nonz_cap_to xa s \<and> ex_nonz_cap_to a s \<and> ko = TCB tcb
                     \<and> sc_tcb_sc_at (op = None) xa s \<and> bound_sc_tcb_at (op = None) a s)) a s) =
   (tcb_at a s \<and> (bound_sc_tcb_at (\<lambda>sc. sc \<noteq> Some xa) a s \<longrightarrow>
                        (ex_nonz_cap_to xa s \<and> ex_nonz_cap_to a s \<and>
                         sc_tcb_sc_at (op = None) xa s \<and> bound_sc_tcb_at (op = None) a s)))"
  by (auto simp: obj_at_def is_tcb pred_tcb_at_def)

lemma thread_set_mcp_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to a\<rbrace> thread_set (tcb_mcpriority_update g) t \<lbrace>\<lambda>rv. ex_nonz_cap_to a\<rbrace>"
  by (wpsimp wp: ex_nonz_cap_to_pres thread_set_cte_wp_at_trivial simp: tcb_cap_cases_def)

lemma thread_set_mcp_sc_tcb_sc_at[wp]:
  "\<lbrace>sc_tcb_sc_at P a\<rbrace> thread_set (tcb_mcpriority_update g) t \<lbrace>\<lambda>rv. sc_tcb_sc_at P a\<rbrace>"
  by (wpsimp wp: thread_set_obj_at_impossible simp: sc_tcb_sc_at_def)

lemma is_cnode_or_valid_arch_simps[simp]:
  "is_cnode_or_valid_arch (CNodeCap r bits ga)"
  "is_cnode_or_valid_arch (ArchObjectCap (PageDirectoryCap r (Some ab)))"
  by (simp add: is_cnode_or_valid_arch_def is_cap_simps)+

lemma is_nondevice_page_cap_simps[simp]:
  "is_nondevice_page_cap (ArchObjectCap (PageCap False x32 x33 x34 x35))"
  by (simp add: is_cap_simps')

lemma tc_invs[Tcb_AI_asms]:
  "\<lbrace>invs and tcb_at a and ex_nonz_cap_to a
       and (case_option \<top> (valid_cap o fst) e)
       and (case_option \<top> (valid_cap o fst) f)
       and (case_option \<top> (valid_cap o fst) fh)
       and (case_option \<top> (valid_cap o fst) th)
       and (case_option \<top> (case_option \<top> (valid_cap o fst) o snd) g)
       and (case_option \<top> (cte_at o snd) e)
       and (case_option \<top> (cte_at o snd) f)
       and (case_option \<top> (cte_at o snd) fh)
       and (case_option \<top> (cte_at o snd) th)
       and (case_option \<top> (case_option \<top> (cte_at o snd) o snd) g)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) e)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) f)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) fh)
       and (case_option \<top> (no_cap_to_obj_dr_emp o fst) th)
       and (case_option \<top> (case_option \<top> (no_cap_to_obj_dr_emp o fst) o snd) g)
       (* only set prio \<le> mcp of authorising thread *)
       and (\<lambda>s. case_option True (\<lambda>(pr, auth). mcpriority_tcb_at (\<lambda>mcp. pr \<le> mcp) auth s) pr)
       (* only set mcp \<le> mcp of authorising thread *)
       and (\<lambda>s. case_option True (\<lambda>(mcp, auth). mcpriority_tcb_at (\<lambda>m. mcp \<le> m) auth s) mcp)
       and (case_option \<top> (case_option \<top> (\<lambda>sc. bound_sc_tcb_at (op = None) a and ex_nonz_cap_to sc and sc_tcb_sc_at (op = None) sc)) sc)
       and K (case_option True (is_cnode_cap o fst) e)
       and K (case_option True (is_valid_vtable_root o fst) f)
       and K (case_option True (\<lambda>v. case_option True
                          ((swp valid_ipc_buffer_cap (fst v)
                             and is_arch_cap and is_cnode_or_valid_arch)
                                o fst) (snd v)) g)
       and K (case_option True ((is_cnode_or_valid_arch and (is_ep_cap or (op = NullCap))) o fst) fh)
       and K (case_option True ((is_cnode_or_valid_arch and (is_ep_cap or (op = NullCap))) o fst) th)\<rbrace>
      invoke_tcb (ThreadControl a sl fh th mcp pr e f g sc)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: split_def set_mcpriority_def install_tcb_cap_def cong: option.case_cong)
  apply (rule hoare_vcg_precond_imp)
   apply wp
  apply (((simp only: simp_thms
        | (simp add: conj_comms del: hoare_True_E_R,
                  strengthen imp_consequent[where Q="x = None" for x], simp cong: conj_cong)
        | rule wp_split_const_if wp_split_const_if_R
                   hoare_vcg_all_lift_R
                   hoare_vcg_E_elim hoare_vcg_const_imp_lift_R
                   hoare_vcg_R_conj allI hoare_vcg_imp_lift'
        | (wp out_invs_trivial case_option_wpE cap_delete_deletes
             cap_delete_valid_cap cap_insert_valid_cap out_cte_at
             cap_insert_cte_at cap_delete_cte_at out_valid_cap
             hoare_vcg_const_imp_lift_R hoare_vcg_all_lift_R
             thread_set_tcb_ipc_buffer_cap_cleared_invs
             thread_set_invs_trivial[OF ball_tcb_cap_casesI]
             hoare_vcg_all_lift thread_set_valid_cap
             check_cap_inv [where P="valid_cap c" for c]
             check_cap_inv [where P="tcb_cap_valid c p" for c p]
             check_cap_inv[where P="cte_at p0" for p0]
             check_cap_inv[where P="tcb_at p0" for p0]
             thread_set_cte_at tcb_at_typ_at
             thread_set_cte_wp_at_trivial[where Q="\<lambda>x. x", OF ball_tcb_cap_casesI]
             thread_set_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_no_change_tcb_sched_context
             checked_insert_no_cap_to
             checked_insert_tcb_invs
             out_no_cap_to_trivial[OF ball_tcb_cap_casesI]
             thread_set_ipc_tcb_cap_valid
             static_imp_wp static_imp_conj_wp
             sched_context_unbind_tcb_invs
             TcbAcc_AI.gbn_wp)[1]
        | simp add: ran_tcb_cap_cases dom_tcb_cap_cases[simplified] horridly_specific_rewrite not_pred_tcb tcb_at_typ
               del: hoare_True_E_R
        | wpc
        | strengthen use_no_cap_to_obj_asid_strg
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index 0"]
                     tcb_cap_valid_ep_strgs
                     tcb_cap_always_valid_strg[where p="tcb_cnode_index (Suc 0)"]))+)
 (* FIXME RT: needs preconditions for sched_context_bind and sched_context_unbind *)
  apply (intro conjI impI; clarsimp?;
    (clarsimp simp: tcb_at_cte_at_0 tcb_at_cte_at_1[simplified]
                        is_cap_simps is_valid_vtable_root_def
                        tcb_cap_valid_def
                        invs_valid_objs cap_asid_def vs_cap_ref_def
                        case_bool_If valid_ipc_buffer_cap_def
                       | split arch_cap.splits if_splits option.split_asm)+)
  done


lemma check_valid_ipc_buffer_inv:
  "\<lbrace>P\<rbrace> check_valid_ipc_buffer vptr cap \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def split del: if_split | wpcw)+
  done

lemma check_valid_ipc_buffer_wp[Tcb_AI_asms]:
  "\<lbrace>\<lambda>(s::'state_ext::state_ext state). is_arch_cap cap \<and> is_cnode_or_valid_arch cap
          \<and> valid_ipc_buffer_cap cap vptr
          \<and> is_aligned vptr msg_align_bits
             \<longrightarrow> P s\<rbrace>
     check_valid_ipc_buffer vptr cap
   \<lbrace>\<lambda>rv. P\<rbrace>,-"
  apply (simp add: check_valid_ipc_buffer_def whenE_def
             cong: cap.case_cong arch_cap.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp | simp add: whenE_def split del: if_split | wpc)+
  apply (clarsimp simp: is_cap_simps is_cnode_or_valid_arch_def
                        valid_ipc_buffer_cap_def)
  done

lemma derive_no_cap_asid[wp,Tcb_AI_asms]:
  "\<lbrace>(no_cap_to_obj_with_diff_ref cap S)::'state_ext::state_ext state\<Rightarrow>bool\<rbrace>
     derive_cap slot cap
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref rv S\<rbrace>,-"
  apply (simp add: derive_cap_def arch_derive_cap_def
             cong: cap.case_cong)
  apply (rule hoare_pre)
   apply (wp | simp | wpc)+
  apply (auto simp add: no_cap_to_obj_with_diff_ref_Null,
         auto simp add: no_cap_to_obj_with_diff_ref_def
                        table_cap_ref_def)
  done


lemma decode_set_ipc_inv[wp,Tcb_AI_asms]:
  "\<lbrace>P::'state_ext::state_ext state \<Rightarrow> bool\<rbrace> decode_set_ipc_buffer args cap slot excaps \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp   add: decode_set_ipc_buffer_def whenE_def
                     split_def
          split del: if_split)
  apply (rule hoare_pre, wp check_valid_ipc_buffer_inv)
  apply simp
  done

lemma no_cap_to_obj_with_diff_ref_update_cap_data[Tcb_AI_asms]:
  "no_cap_to_obj_with_diff_ref c S s \<longrightarrow>
    no_cap_to_obj_with_diff_ref (update_cap_data P x c) S s"
  apply (case_tac "update_cap_data P x c = NullCap")
   apply (simp add: no_cap_to_obj_with_diff_ref_Null)
  apply (subgoal_tac "vs_cap_ref (update_cap_data P x c)
                                 = vs_cap_ref c")
   apply (simp add: no_cap_to_obj_with_diff_ref_def
                    update_cap_objrefs)
  apply (clarsimp simp: update_cap_data_closedform
                        table_cap_ref_def
                        arch_update_cap_data_def
                 split: cap.split)
  apply simp
  done


lemma update_cap_valid[Tcb_AI_asms]:
  "valid_cap cap (s::'state_ext::state_ext state) \<Longrightarrow>
   valid_cap (case capdata of
              None \<Rightarrow> cap_rights_update rs cap
            | Some x \<Rightarrow> update_cap_data p x
                     (cap_rights_update rs cap)) s"
  apply (case_tac capdata, simp_all)[1]
  apply (case_tac cap,
         simp_all add: update_cap_data_def cap_rights_update_def
                       is_cap_defs Let_def split_def valid_cap_def
                       badge_update_def the_cnode_cap_def cap_aligned_def
                       arch_update_cap_data_def
            split del: if_split)
     apply (simp add: badge_update_def cap_rights_update_def)
    apply (simp add: badge_update_def)
   apply (simp add: word_bits_def)
  apply (rename_tac arch_cap)
  using valid_validate_vm_rights[simplified valid_vm_rights_def]
  apply (case_tac arch_cap, simp_all add: acap_rights_update_def
                                     split: option.splits prod.splits)
  done


crunch pred_tcb_at: switch_to_thread "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at[wp]: set_priority "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv hoare_drop_imps)
crunch typ_at[wp]: invoke_tcb "\<lambda>s. P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_x_wp' check_cap_inv maybeM_inv
     simp: crunch_simps)

end

context begin interpretation Arch .
requalify_consts is_cnode_or_valid_arch
requalify_facts invoke_tcb_typ_at
end

global_interpretation Tcb_AI?: Tcb_AI
  where is_cnode_or_valid_arch = ARM.is_cnode_or_valid_arch
 proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (unfold_locales; fact Tcb_AI_asms)
qed

end
