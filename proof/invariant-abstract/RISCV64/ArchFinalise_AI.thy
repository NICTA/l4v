(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchFinalise_AI
imports "../Finalise_AI"
begin

(* FIXME: MOVE *)
lemma hoare_validE_R_conjI:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, - ; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>, - \<rbrakk>  \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>, -"
  by (auto simp: Ball_def validE_R_def validE_def valid_def)

context Arch begin

named_theorems Finalise_AI_asms

crunch caps_of_state[wp]: prepare_thread_delete "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps)

declare prepare_thread_delete_caps_of_state [Finalise_AI_asms]

global_naming RISCV64

lemma valid_global_refs_asid_table_udapte [iff]:
  "valid_global_refs (s\<lparr>arch_state := riscv_asid_table_update f (arch_state s)\<rparr>) =
  valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma nat_to_cref_unat_of_bl':
  "\<lbrakk> length xs < 64; n = length xs \<rbrakk> \<Longrightarrow>
   nat_to_cref n (unat (of_bl xs :: machine_word)) = xs"
  apply (simp add: nat_to_cref_def word_bits_def)
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (subst to_bl_nth)
   apply (simp add: word_size)
  apply (simp add: word_size)
  apply (simp add: test_bit_of_bl rev_nth)
  apply fastforce
  done

lemmas nat_to_cref_unat_of_bl = nat_to_cref_unat_of_bl' [OF _ refl]

lemma riscv_global_pt_asid_table_update[simp]:
  "riscv_global_pt (arch_state s\<lparr>riscv_asid_table := atable\<rparr>) = riscv_global_pt (arch_state s)"
  by (simp add: riscv_global_pt_def)

lemma equal_kernel_mappings_asid_table_unmap:
  "equal_kernel_mappings s
   \<Longrightarrow> equal_kernel_mappings (s\<lparr>arch_state := arch_state s
                                \<lparr>riscv_asid_table := (asid_table s)(i := None)\<rparr>\<rparr>)"
  unfolding equal_kernel_mappings_def
  apply clarsimp
  apply (erule_tac x=asid in allE)
  apply (erule_tac x=pt_ptr in allE)
  apply (clarsimp simp: fun_upd_def)
  apply (erule impE)
   subgoal by (clarsimp simp: vspace_for_asid_def in_omonad pool_for_asid_def split: if_splits)
  apply (clarsimp simp: has_kernel_mappings_def)
  done

lemma invs_riscv_asid_table_unmap:
  "invs s \<and> is_aligned base asid_low_bits
       \<and> tab = riscv_asid_table (arch_state s)
     \<longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (strengthen valid_asid_map_unmap valid_vspace_objs_unmap_strg
                    valid_vs_lookup_unmap_strg valid_arch_state_unmap_strg)
  apply (simp add: valid_irq_node_def valid_kernel_mappings_def)
  apply (simp add: valid_table_caps_def valid_machine_state_def valid_global_objs_def
                   valid_asid_pool_caps_def equal_kernel_mappings_asid_table_unmap)
  done

lemma delete_asid_pool_invs[wp]:
  "delete_asid_pool base pptr \<lbrace>invs\<rbrace>"
  unfolding delete_asid_pool_def
  supply fun_upd_apply[simp del]
  apply wpsimp
  apply (strengthen invs_riscv_asid_table_unmap)
  apply (simp add: asid_low_bits_of_def asid_low_bits_def ucast_zero_is_aligned)
  done

lemma do_machine_op_pool_for_asid[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: pool_for_asid_def)

lemma do_machine_op_vspace_for_asid[wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wpsimp simp: vspace_for_asid_def obind_def
             wp: conjI hoare_vcg_all_lift hoare_vcg_imp_lift'
             split: option.splits)

lemma set_vm_root_pool_for_asid[wp]:
  "set_vm_root pt \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  by (wpsimp simp: set_vm_root_def wp: get_cap_wp)

lemma set_vm_root_vspace_for_asid[wp]:
  "set_vm_root pt \<lbrace> \<lambda>s. P (vspace_for_asid asid s) \<rbrace>"
  by (wpsimp simp: set_vm_root_def wp: get_cap_wp)

lemma clearExMonitor_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (hwASIDFlush a) \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: dmo_invs
             simp: hwASIDFlush_def machine_op_lift_def
                   machine_rest_lift_def in_monad select_f_def)

lemma delete_asid_invs[wp]:
  "\<lbrace> invs and valid_asid_table and pspace_aligned \<rbrace>delete_asid asid pd \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_asid_def cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_invs_unmap)
  apply blast
  done

lemma delete_asid_pool_unmapped[wp]:
  "\<lbrace>\<lambda>s. pool_for_asid asid s = Some poolptr \<rbrace>
     delete_asid_pool asid poolptr
   \<lbrace>\<lambda>_ s. pool_for_asid asid s = None \<rbrace>"
  unfolding delete_asid_pool_def
  by (wpsimp simp: pool_for_asid_def)

lemma set_asid_pool_unmap:
  "\<lbrace>\<lambda>s. pool_for_asid asid s = Some poolptr \<rbrace>
   set_asid_pool poolptr (pool(asid_low_bits_of asid := None))
   \<lbrace>\<lambda>rv s. vspace_for_asid asid s = None \<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  by (simp add: pool_for_asid_def vspace_for_asid_def vspace_for_pool_def obind_def in_omonad
         split: option.splits)

lemma delete_asid_unmapped[wp]:
  "\<lbrace>\<lambda>s. vspace_for_asid asid s = Some pt\<rbrace>
   delete_asid asid pt
   \<lbrace>\<lambda>_ s. vspace_for_asid asid s = None\<rbrace>"
  unfolding delete_asid_def
  apply (simp cong: option.case_cong)
  apply (wpsimp wp: set_asid_pool_unmap)
  apply (clarsimp simp: vspace_for_asid_def pool_for_asid_def vspace_for_pool_def
                        obind_def in_omonad obj_at_def
                 split: option.splits)
  done

lemma set_pt_tcb_at:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (wpsimp simp: set_pt_def obj_at_def wp: set_object_wp)

crunch tcb_at_arch: unmap_page "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps wp: crunch_wps set_pt_tcb_at ignore: set_object)

lemmas unmap_page_tcb_at = unmap_page_tcb_at_arch

lemma unmap_page_tcb_cap_valid:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap r s\<rbrace>
    unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. tcb_cap_valid cap r s\<rbrace>"
  apply (rule tcb_cap_valid_typ_st)
    apply wp
   apply (simp add: pred_tcb_at_def2)
  apply (wp unmap_page_tcb_at hoare_vcg_ex_lift hoare_vcg_all_lift)+
  done


global_naming Arch

lemma (* replaceable_cdt_update *)[simp,Finalise_AI_asms]:
  "replaceable (cdt_update f s) = replaceable s"
  by (fastforce simp: replaceable_def tcb_cap_valid_def
                      reachable_frame_cap_def reachable_target_def)

lemma (* replaceable_revokable_update *)[simp,Finalise_AI_asms]:
  "replaceable (is_original_cap_update f s) = replaceable s"
  by (fastforce simp: replaceable_def is_final_cap'_def2 tcb_cap_valid_def
                      reachable_frame_cap_def reachable_target_def)

lemma (* replaceable_more_update *) [simp,Finalise_AI_asms]:
  "replaceable (trans_state f s) sl cap cap' = replaceable s sl cap cap'"
  by (simp add: replaceable_def reachable_frame_cap_def reachable_target_def)

lemma reachable_target_trans_state[simp]:
  "reachable_target ref p (trans_state f s) = reachable_target ref p s"
  by (clarsimp simp: reachable_target_def split_def)

lemma reachable_frame_cap_trans_state[simp]:
  "reachable_frame_cap cap (trans_state f s) = reachable_frame_cap cap s"
  by (simp add: reachable_frame_cap_def)

lemmas [Finalise_AI_asms] = obj_refs_obj_ref_of (* used under name obj_ref_ofI *)

lemma (* empty_slot_invs *) [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s sl cap.NullCap) sl s \<and>
        emptyable sl s \<and>
        (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre info ((caps_of_state s) (sl \<mapsto> NullCap)))\<rbrace>
     empty_slot sl info
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: empty_slot_def set_cdt_def bind_assoc cong: if_cong)
  apply (wp post_cap_deletion_invs)
        apply (simp add: invs_def valid_state_def valid_mdb_def2)
        apply (wp replace_cap_valid_pspace set_cap_caps_of_state2
                  replace_cap_ifunsafe get_cap_wp
                  set_cap_idle valid_irq_node_typ set_cap_typ_at
                  set_cap_irq_handlers set_cap_valid_arch_caps
                  set_cap_cap_refs_respects_device_region_NullCap
               | simp add: trans_state_update[symmetric]
                      del: trans_state_update fun_upd_apply
                      split del: if_split)+
  apply (clarsimp simp: is_final_cap'_def2 simp del: fun_upd_apply)
  apply (clarsimp simp: conj_comms invs_def valid_state_def valid_mdb_def2)
  apply (subgoal_tac "mdb_empty_abs s")
   prefer 2
   apply (rule mdb_empty_abs.intro)
   apply (rule vmdb_abs.intro)
   apply (simp add: valid_mdb_def swp_def cte_wp_at_caps_of_state conj_comms)
  apply (clarsimp simp: untyped_mdb_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n
                        valid_pspace_def cap_range_def)
  apply (clarsimp simp: untyped_inc_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n)
  apply (simp add: ut_revocable_def cur_tcb_def valid_irq_node_def
                   no_cap_to_obj_with_diff_ref_Null)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_mdb_def)
  apply (rule conjI)
   apply (clarsimp simp: irq_revocable_def)
  apply (rule conjI)
   apply (clarsimp simp: reply_master_revocable_def)
  apply (thin_tac "info \<noteq> NullCap \<longrightarrow> P info" for P)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state_def)
  apply (rule conjI)
   apply (clarsimp simp:descendants_inc_def mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (clarsimp simp: reply_mdb_def)
   apply (rule conjI)
    apply (unfold reply_caps_mdb_def)[1]
    apply (rule allEI, assumption)
    apply (fold reply_caps_mdb_def)[1]
    apply (case_tac "sl = ptr", simp)
    apply (simp add: fun_upd_def split del: if_split del: split_paired_Ex)
    apply (erule allEI, rule impI, erule(1) impE)
    apply (erule exEI)
    apply (simp, rule ccontr)
    apply (erule(5) emptyable_no_reply_cap)
    apply simp
   apply (unfold reply_masters_mdb_def)[1]
   apply (elim allEI)
   apply (clarsimp simp: mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (simp add: valid_ioc_def)
  apply (rule conjI)
   apply (clarsimp simp: tcb_cap_valid_def
                  dest!: emptyable_valid_NullCapD)
  apply (rule conjI)
   apply (clarsimp simp: mdb_cte_at_def cte_wp_at_caps_of_state)
   apply (cases sl)
   apply (rule conjI, clarsimp)
    apply (subgoal_tac "cdt s \<Turnstile> (ab,bb) \<rightarrow> (ab,bb)")
     apply (simp add: no_mloop_def)
    apply (rule r_into_trancl)
    apply (simp add: cdt_parent_of_def)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_caps_of_state replaceable_def
                        reachable_frame_cap_def reachable_target_def
                   del: allI)
  apply (case_tac "is_final_cap' cap s")
   apply auto[1]
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  by fastforce

lemma dom_tcb_cap_cases_lt_ARCH [Finalise_AI_asms]:
  "dom tcb_cap_cases = {xs. length xs = 3 \<and> unat (of_bl xs :: machine_word) < 5}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1 split: if_split_asm)
  apply clarsimp
  apply (frule tcb_cap_cases_lt)
  apply (clarsimp simp: nat_to_cref_unat_of_bl')
  done

lemma (* unbind_notification_final *) [wp,Finalise_AI_asms]:
  "\<lbrace>is_final_cap' cap\<rbrace> unbind_notification t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding unbind_notification_def
  apply (wp final_cap_lift thread_set_caps_of_state_trivial hoare_drop_imps
       | wpc | simp add: tcb_cap_cases_def)+
  done

lemma arch_thread_set_caps_of_state[wp]:
  "arch_thread_set v t \<lbrace>\<lambda>s. P (caps_of_state s) \<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: fun_upd_def)
  apply (frule get_tcb_ko_atD)
  apply (auto simp: caps_of_state_after_update obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_final_cap[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> arch_thread_set v t \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  by (wpsimp simp: is_final_cap'_def2 cte_wp_at_caps_of_state)

lemma arch_thread_get_final_cap[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> arch_thread_get v t \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply (simp add: arch_thread_get_def is_final_cap'_def2 cte_wp_at_caps_of_state, wp)
  apply auto
  done

lemma prepare_thread_delete_final[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> prepare_thread_delete t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding prepare_thread_delete_def by wp

lemma (* finalise_cap_cases1 *)[Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. final \<longrightarrow> is_final_cap' cap s
         \<and> cte_wp_at ((=) cap) slot s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv s. fst rv = cap.NullCap
         \<and> snd rv = (if final then cap_cleanup_opt cap else NullCap)
         \<and> (snd rv \<noteq> NullCap \<longrightarrow> is_final_cap' cap s)
     \<or>
       is_zombie (fst rv) \<and> is_final_cap' cap s
        \<and> snd rv = NullCap
        \<and> appropriate_cte_cap (fst rv) = appropriate_cte_cap cap
        \<and> cte_refs (fst rv) = cte_refs cap
        \<and> gen_obj_refs (fst rv) = gen_obj_refs cap
        \<and> obj_size (fst rv) = obj_size cap
        \<and> fst_cte_ptrs (fst rv) = fst_cte_ptrs cap
        \<and> vs_cap_ref cap = None\<rbrace>"
  apply (cases cap, simp_all split del: if_split cong: if_cong)
            apply ((wp suspend_final_cap[where sl=slot]
                      deleting_irq_handler_final[where slot=slot]
                      | simp add: o_def is_cap_simps fst_cte_ptrs_def
                                  dom_tcb_cap_cases_lt_ARCH tcb_cnode_index_def
                                  can_fast_finalise_def
                                  appropriate_cte_cap_def gen_obj_refs_def
                                  vs_cap_ref_def cap_cleanup_opt_def
                      | intro impI TrueI ext conjI)+)[11]
  sorry (* FIXME RISCV
  apply (simp add: arch_finalise_cap_def split del: if_split)
  apply (rule hoare_pre)
   apply (wpsimp simp: cap_cleanup_opt_def arch_cap_cleanup_opt_def simp_thms)+
  done *)

crunch typ_at_arch [wp]: arch_thread_set "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps set_object_typ_at)

crunch typ_at[wp,Finalise_AI_asms]: arch_finalise_cap "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: maskInterrupt set_object)

crunch typ_at[wp,Finalise_AI_asms]: prepare_thread_delete "\<lambda>s. P (typ_at T p s)"

crunch tcb_at[wp]: arch_thread_set "\<lambda>s. tcb_at p s"
  (ignore: set_object)

crunch tcb_at[wp]: arch_thread_get "\<lambda>s. tcb_at p s"

crunch tcb_at[wp]: prepare_thread_delete "\<lambda>s. tcb_at p s"

lemma (* finalise_cap_new_valid_cap *)[wp,Finalise_AI_asms]:
  "\<lbrace>valid_cap cap\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  apply (cases cap; simp)
            apply (wp suspend_valid_cap prepare_thread_delete_typ_at
                     | simp add: o_def valid_cap_def cap_aligned_def
                                 valid_cap_Null_ext
                           split del: if_split
                     | clarsimp | rule conjI)+
  (* ArchObjectCap *)
  apply (wpsimp wp: o_def valid_cap_def cap_aligned_def
                 split_del: if_split
         | clarsimp simp: arch_finalise_cap_def)+
  done

crunch inv[wp]: arch_thread_get "P"

lemma hoare_split: "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. Q r and Q' r\<rbrace>"
  by (auto simp: valid_def)

sublocale
  arch_thread_set: non_aobj_non_cap_non_mem_op "arch_thread_set f v"
  by (unfold_locales;
        ((wpsimp)?;
        wpsimp wp: set_object_non_arch simp: non_arch_objs arch_thread_set_def)?)

(* arch_thread_set invariants *)
lemma arch_thread_set_cur_tcb[wp]: "\<lbrace>cur_tcb\<rbrace> arch_thread_set p v \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  unfolding cur_tcb_def[abs_def]
  apply (rule hoare_lift_Pf [where f=cur_thread])
   apply (simp add: tcb_at_typ)
   apply wp
  apply (simp add: arch_thread_set_def)
  apply (wp hoare_drop_imp)
  apply simp
  done

lemma cte_wp_at_update_some_tcb:
  "\<lbrakk>kheap s v = Some (TCB tcb) ; tcb_cnode_map tcb = tcb_cnode_map (f tcb)\<rbrakk>
  \<Longrightarrow> cte_wp_at P p (s\<lparr>kheap := kheap s (v \<mapsto> TCB (f tcb))\<rparr>) = cte_wp_at P p s"
  apply (clarsimp simp: cte_wp_at_cases2 dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
     arch_thread_set p v
   \<lbrace>\<lambda>s. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD simp del: fun_upd_apply)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (subst cap_refs_respects_region_cong)
    prefer 3
    apply assumption
   apply (rule cte_wp_caps_of_lift)
   apply (subst arch_tcb_update_aux3)
   apply (rule_tac cte_wp_at_update_some_tcb, assumption)
   apply (simp add: tcb_cnode_map_def)+
     done

lemma arch_thread_set_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace>
     arch_thread_set p v
   \<lbrace>\<lambda>s. pspace_respects_device_region\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_pspace_respects_device_region)
  apply clarsimp
  done

lemma arch_thread_set_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> arch_thread_set p v \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  unfolding cap_refs_in_kernel_window_def[abs_def]
  apply (rule hoare_lift_Pf [where f="\<lambda>s. not_kernel_window s"])
  apply (rule valid_refs_cte_lift)
  apply wp+
  done

crunch valid_irq_states[wp]: arch_thread_set valid_irq_states
  (wp: crunch_wps simp: crunch_simps)

crunch interrupt_state[wp]: arch_thread_set "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas arch_thread_set_valid_irq_handlers[wp] = valid_irq_handlers_lift[OF arch_thread_set.caps arch_thread_set_interrupt_state]

crunch interrupt_irq_node[wp]: arch_thread_set "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas arch_thread_set_valid_irq_node[wp] = valid_irq_node_typ[OF arch_thread_set_typ_at_arch arch_thread_set_interrupt_irq_node]

crunch idle_thread[wp]: arch_thread_set "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_thread_set_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp+

lemma arch_thread_set_valid_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  by (rule valid_reply_masters_cte_lift) wp

lemma arch_thread_set_pred_tcb_at[wp_unsafe]:
  "\<lbrace>pred_tcb_at proj P t and K (proj_not_field proj tcb_arch_update)\<rbrace>
     arch_thread_set p v
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev
                  dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_valid_reply_caps[wp]:
  "\<lbrace>valid_reply_caps\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  by (rule valid_reply_caps_st_cte_lift)
     (wpsimp wp: arch_thread_set_pred_tcb_at)+

lemma arch_thread_set_if_unsafe_then_cap[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_ifunsafe)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                  dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev)
  apply assumption
  apply simp
  apply (subst get_tcb_rev, assumption, simp)+
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wpsimp wp: only_idle_lift set_asid_pool_typ_at
                 arch_thread_set_pred_tcb_at)

lemma arch_thread_set_valid_idle[wp]:
  "arch_thread_set f t \<lbrace>valid_idle\<rbrace>"
  by (wpsimp simp: arch_thread_set_def set_object_def valid_idle_def valid_arch_idle_def
                   get_tcb_def pred_tcb_at_def obj_at_def pred_neg_def)

lemma arch_thread_set_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp add: valid_ioc_def
                  simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits
                  dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (subst arch_tcb_update_aux3)
  apply (subst cte_wp_at_update_some_tcb,assumption)
   apply (clarsimp simp: tcb_cnode_map_def)+
  done

lemma arch_thread_set_valid_mdb[wp]: "\<lbrace>valid_mdb\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift get_object_wp simp: arch_thread_set_def set_object_def)

lemma arch_thread_set_zombies_final[wp]: "\<lbrace>zombies_final\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                  dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev)
  apply assumption
  apply simp
  apply (subst get_tcb_rev, assumption, simp)+
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> arch_thread_set f v \<lbrace>\<lambda>_.pspace_in_kernel_window\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift, wp+)

lemma arch_thread_set_pspace_distinct[wp]: "\<lbrace>pspace_distinct\<rbrace>arch_thread_set f v\<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_distinct)
  apply (clarsimp simp: get_object_def obj_at_def
                  dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> arch_thread_set f v \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_aligned)
  apply (clarsimp simp: obj_at_def get_object_def
                  dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_valid_objs_context[wp]:
  "arch_thread_set (tcb_context_update f) v \<lbrace>valid_objs\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_valid_objs)
  apply (clarsimp simp: Ball_def obj_at_def valid_objs_def dest!: get_tcb_SomeD)
  apply (erule_tac x=v in allE)
  apply (clarsimp simp: dom_def)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (clarsimp simp:valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma sym_refs_update_some_tcb:
  "\<lbrakk>kheap s v = Some (TCB tcb) ; refs_of (TCB tcb) = refs_of (TCB (f tcb))\<rbrakk>
  \<Longrightarrow> sym_refs (state_refs_of (s\<lparr>kheap := kheap s (v \<mapsto> TCB (f tcb))\<rparr>)) = sym_refs (state_refs_of s)"
  apply (rule_tac f=sym_refs in arg_cong)
  apply (rule all_ext)
  apply (clarsimp simp: sym_refs_def state_refs_of_def)
  done

lemma arch_thread_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace> arch_thread_set f p \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (subst arch_tcb_update_aux3)
  apply (subst sym_refs_update_some_tcb[where f="tcb_arch_update f"])
    apply assumption
   apply (clarsimp simp: refs_of_def)
  apply assumption
  done

lemma as_user_unlive_hyp[wp]:
  "\<lbrace>obj_at (Not \<circ> hyp_live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def hyp_live_def arch_tcb_context_set_def)

lemma as_user_unlive0[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live0) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def arch_tcb_context_set_def dest!: get_tcb_SomeD)

lemma o_def_not: "obj_at (\<lambda>a. \<not> P a) t s =  obj_at (Not o P) t s"
  by (simp add: obj_at_def)

lemma arch_thread_set_if_live_then_nonz_cap':
  "\<forall>y. hyp_live (TCB (y\<lparr>tcb_arch := p (tcb_arch y)\<rparr>)) \<longrightarrow> hyp_live (TCB y) \<Longrightarrow>
   \<lbrace>if_live_then_nonz_cap\<rbrace> arch_thread_set p v \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_iflive)
  apply (clarsimp simp: ex_nonz_cap_to_def if_live_then_nonz_cap_def
                  dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  apply (erule_tac x=v in allE, drule mp; assumption?)
  apply (clarsimp simp: live_def)
  done

lemma same_caps_tcb_arch_update[simp]:
  "same_caps (TCB (tcb_arch_update f tcb)) = same_caps (TCB tcb)"
  by (rule ext) (clarsimp simp: tcb_cap_cases_def)

lemma as_user_valid_irq_node[wp]:
  "\<lbrace>valid_irq_node\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_irq_node\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: valid_irq_node_def obj_at_def is_cap_table dest!: get_tcb_SomeD)
  by (metis kernel_object.distinct(1) option.inject)

lemma dmo_machine_state_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>rv s. Q rv (machine_state s)\<rbrace>"
  unfolding do_machine_op_def by wpsimp (erule use_valid; assumption)

lemma as_user_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_irq_states\<rbrace>"
  unfolding as_user_def
  by (wpsimp wp: set_object_wp simp: obj_at_def valid_irq_states_def)

lemma as_user_ioc[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> as_user t f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  unfolding as_user_def by (wpsimp wp: set_object_wp)

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user t f \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  unfolding valid_ioc_def by (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift)

lemma arch_finalise_cap_invs' [wp,Finalise_AI_asms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap cap)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_invs | wpc)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (auto simp: mask_def vmsz_aligned_def wellformed_mapdata_def)
  done

lemma as_user_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live) vr\<rbrace> as_user t f \<lbrace>\<lambda>_. obj_at (Not \<circ> live) vr\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp)
  by (clarsimp simp: obj_at_def live_def hyp_live_def arch_tcb_context_set_def dest!: get_tcb_SomeD)

lemma obj_at_not_live_valid_arch_cap_strg [Finalise_AI_asms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: valid_cap_def obj_at_def valid_arch_cap_ref_def
                     a_type_arch_live live_def hyp_live_def
              split: arch_cap.split_asm if_splits)

lemma delete_asid_pool_not_reachable[wp]:
  "\<lbrace> \<lambda>s. pool_for_asid asid s = Some ptr \<rbrace>
   delete_asid_pool asid ptr
   \<lbrace>\<lambda>rv s. \<not> reachable_target (asid, 0) ptr s\<rbrace>"
  apply (simp add: reachable_target_def)
  apply (rule hoare_strengthen_post)
   apply (rule delete_asid_pool_unmapped)
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def split: if_split_asm)
  done

lemmas reachable_frame_cap_simps =
  reachable_frame_cap_def[unfolded is_frame_cap_def arch_cap_fun_lift_def, split_simps cap.split]

lemma arch_finalise_cap_replaceable1:
  notes strg = tcb_cap_valid_imp_NullCap
               obj_at_not_live_valid_arch_cap_strg[where cap=cap]
  notes simps = replaceable_def and_not_not_or_imp
                (* FIXME RISCV:
                vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                vs_lookup_pages_eq_ap[THEN fun_cong, symmetric] *)
                is_cap_simps vs_cap_ref_def
                no_cap_to_obj_with_diff_ref_Null o_def
                reachable_frame_cap_simps
  notes wps = hoare_drop_imp[where R="%_. is_final_cap' cap" for cap]
              unmap_page_table_unmapped2 valid_cap_typ
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> ArchObjectCap cap \<and>
          x = is_final_cap' (ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and> valid_asid_table s\<rbrace>
     arch_finalise_cap cap x
     \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (wpsimp simp: simps wp: wps | strengthen strg)+
  sorry
  (* FIXME RISCV
  apply (rule hoare_pre)
   apply (simp add: simps split: option.splits vmpage_size.splits)
   apply (wp wps
          | strengthen strg
          | simp add: simps reachable_frame_cap_def live_def
          | wpc)+
     (* unmap_page case is a bit unpleasant *)
     apply (strengthen cases_conj_strg[where P="\<not> is_final_cap' cap s" for cap s, simplified])
     apply (rule hoare_post_imp, clarsimp split: vmpage_size.split, assumption)
     apply (simp add: vspace_bits_defs)
     apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_const_imp_lift
               unmap_page_tcb_cap_valid unmap_page_page_unmapped
                   unmap_page_section_unmapped)[1]
    apply (wp wps
           | strengthen strg imp_and_strg tcb_cap_valid_imp_NullCap
           | simp add: simps is_master_reply_cap_def reachable_pg_cap_def
           | wpc)+
  apply (intro conjI; clarsimp split: cap.splits arch_cap.splits vmpage_size.splits)
  by (auto simp: valid_cap_def obj_at_def simps is_master_reply_cap_def
                    a_type_def data_at_def vspace_bits_defs X
             elim!: tcb_cap_valid_imp_NullCap[rule_format, rotated]
             split: cap.splits arch_cap.splits vmpage_size.splits) *)


global_naming Arch
lemma (* deleting_irq_handler_slot_not_irq_node *)[Finalise_AI_asms]:
  "\<lbrace>if_unsafe_then_cap and valid_global_refs
           and cte_wp_at (\<lambda>cp. cap_irqs cp \<noteq> {}) sl\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv s. (interrupt_irq_node s irq, []) \<noteq> sl\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply wp
  apply clarsimp
  apply (drule(1) if_unsafe_then_capD)
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (drule cte_refs_obj_refs_elem)
  apply (erule disjE)
   apply simp
   apply (drule(1) valid_global_refsD[OF _ caps_of_state_cteD])
    prefer 2
    apply (erule notE, simp add: cap_range_def, erule disjI2)
   apply (simp add: global_refs_def)
  apply (clarsimp simp: appropriate_cte_cap_def split: cap.split_asm)
  done

lemma no_cap_to_obj_with_diff_ref_finalI_ARCH[Finalise_AI_asms]:
  "\<lbrakk> cte_wp_at ((=) cap) p s; is_final_cap' cap s;
            obj_refs cap' = obj_refs cap \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (case_tac "obj_refs cap = {}")
   apply (case_tac "cap_irqs cap = {}")
    apply (case_tac "arch_gen_refs cap = {}")
     apply (simp add: is_final_cap'_def)
     apply (case_tac cap, simp_all add: gen_obj_refs_def)
    apply ((clarsimp simp add: no_cap_to_obj_with_diff_ref_def
                              cte_wp_at_caps_of_state
                              vs_cap_ref_def
                       dest!: obj_ref_none_no_asid[rule_format])+)[2]
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        is_final_cap'_def2
              simp del: split_paired_All)
  apply (frule_tac x=p in spec)
  apply (drule_tac x="(a, b)" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        gen_obj_refs_Int)
  done

lemma (* suspend_no_cap_to_obj_ref *)[wp,Finalise_AI_asms]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   cte_wp_at_caps_of_state)
  apply (wp suspend_caps_of_state)
  apply (clarsimp dest!: obj_ref_none_no_asid[rule_format])
  done

lemma prepare_thread_delete_no_cap_to_obj_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     prepare_thread_delete t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  unfolding prepare_thread_delete_def by wpsimp

lemma prepare_thread_delete_unlive_hyp:
  "\<lbrace>obj_at \<top> ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> hyp_live) ptr\<rbrace>"
  apply (simp add: prepare_thread_delete_def)
  apply (wpsimp simp: obj_at_def is_tcb_def hyp_live_def)
  done

lemma prepare_thread_delete_unlive0:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live0) ptr\<rbrace>"
  by (simp add: prepare_thread_delete_def)

lemma prepare_thread_delete_unlive[wp]:
  "\<lbrace>obj_at (Not \<circ> live0) ptr\<rbrace> prepare_thread_delete ptr \<lbrace>\<lambda>rv. obj_at (Not \<circ> live) ptr\<rbrace>"
  apply (rule_tac Q="\<lambda>rv. obj_at (Not \<circ> live0) ptr and obj_at (Not \<circ> hyp_live) ptr" in hoare_strengthen_post)
  apply (wpsimp wp: hoare_vcg_conj_lift prepare_thread_delete_unlive_hyp prepare_thread_delete_unlive0)
   apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: obj_at_def, case_tac ko, simp_all add: is_tcb_def live_def)
  done

lemma arch_finalise_cap_replaceable:
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> ArchObjectCap cap \<and>
          x = is_final_cap' (ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_vspace_objs s \<and> valid_objs s \<and>
          valid_asid_table s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) (ArchObjectCap cap)\<rbrace>"
  by (rule arch_finalise_cap_replaceable1)

lemma (* finalise_cap_replaceable *) [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s \<and> valid_mdb s
        \<and> cte_wp_at ((=) cap) sl s \<and> valid_objs s \<and> sym_refs (state_refs_of s)
        \<and> (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s)
        \<and> (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and>
                               valid_vspace_objs s \<and>
                               valid_arch_state s)\<rbrace>
     finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  sorry (* FIXME RISCV
  apply (cases "is_arch_cap cap")
   apply (clarsimp simp: is_cap_simps)
   apply (wp arch_finalise_cap_replaceable)
   apply (clarsimp simp: replaceable_def reachable_frame_cap_def
                         o_def cap_range_def valid_arch_state_def
                         ran_tcb_cap_cases is_cap_simps
                         gen_obj_refs_subset vs_cap_ref_def
                         all_bool_eq)
  apply ((cases cap;
      simp add: replaceable_def reachable_frame_cap_def
                       split del: if_split;
      rule hoare_pre),

    (wp suspend_unlive[unfolded o_def]
        suspend_final_cap[where sl=sl]
        prepare_thread_delete_unlive[unfolded o_def]
        unbind_maybe_notification_not_bound
        get_simple_ko_ko_at
        unbind_notification_valid_objs
      | clarsimp simp: o_def dom_tcb_cap_cases_lt_ARCH
                        ran_tcb_cap_cases is_cap_simps
                        cap_range_def
                        can_fast_finalise_def
                        gen_obj_refs_subset
                        vs_cap_ref_def
                        valid_ipc_buffer_cap_def
                 dest!: tcb_cap_valid_NullCapD
                 split: Structures_A.thread_state.split_asm
      | simp cong: conj_cong
      | simp cong: rev_conj_cong add: no_cap_to_obj_with_diff_ref_Null
      | (strengthen tcb_cap_valid_imp_NullCap tcb_cap_valid_imp', wp)
      | rule conjI
      | erule cte_wp_at_weakenE tcb_cap_valid_imp'[rule_format, rotated -1]
      | erule(1) no_cap_to_obj_with_diff_ref_finalI_ARCH
      | (wp_once hoare_drop_imps,
          wp_once cancel_all_ipc_unlive[unfolded o_def]
              cancel_all_signals_unlive[unfolded o_def])
      | ((wp_once hoare_drop_imps)?,
         (wp_once hoare_drop_imps)?,
         wp_once deleting_irq_handler_empty)
      | wpc
      | simp add: valid_cap_simps is_nondevice_page_cap_simps)+)
  done *)

lemma (* deleting_irq_handler_cte_preserved *)[Finalise_AI_asms]:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> deleting_irq_handler irq \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_cte_wp_at_preserved | simp add: x)+
  done

lemma arch_thread_set_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> arch_thread_set f t \<lbrace> \<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp del: fun_upd_apply)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (subst arch_tcb_update_aux3)
  apply (subst cte_wp_at_update_some_tcb[where f="tcb_arch_update f"])
    apply (clarsimp simp: tcb_cnode_map_def)+
  done

crunch cte_wp_at[wp,Finalise_AI_asms]: prepare_thread_delete "\<lambda>s. P (cte_wp_at P' p s)"

crunch cte_wp_at[wp,Finalise_AI_asms]: arch_finalise_cap "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def wp: crunch_wps set_object_cte_at
   ignore: arch_thread_set)
end

interpretation Finalise_AI_1?: Finalise_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming RISCV64

lemma fast_finalise_replaceable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s
     \<and> cte_wp_at ((=) cap) sl s \<and> valid_asid_table s
     \<and> valid_mdb s \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
     fast_finalise cap x
   \<lbrace>\<lambda>rv s. cte_wp_at (replaceable s sl cap.NullCap) sl s\<rbrace>"
  apply (cases "cap_irqs cap = {}")
   apply (simp add: fast_finalise_def2)
   apply wp
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finalise_cap_replaceable[where sl=sl])
     apply (rule finalise_cap_equal_cap[where sl=sl])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply wp
   apply (clarsimp simp: is_cap_simps can_fast_finalise_def)
  apply (clarsimp simp: cap_irqs_def cap_irq_opt_def split: cap.split_asm)
  done

global_naming Arch
lemma (* cap_delete_one_invs *) [Finalise_AI_asms,wp]:
  "\<lbrace>invs and emptyable ptr\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (rule hoare_pre)
  apply (wp empty_slot_invs get_cap_wp)
  apply clarsimp
  apply (drule cte_wp_at_valid_objs_valid_cap, fastforce+)
  done

end

interpretation Finalise_AI_2?: Finalise_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming RISCV64

crunch irq_node[Finalise_AI_asms,wp]: prepare_thread_delete "\<lambda>s. P (interrupt_irq_node s)"

crunch irq_node[wp]: arch_finalise_cap "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps wp: crunch_wps)

crunch pred_tcb_at[wp]:
  delete_asid_pool, delete_asid, unmap_page_table, unmap_page
  "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps test)

crunch pred_tcb_at[wp_unsafe]: arch_finalise_cap "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps)

lemma store_pte_unmap_empty: (* FIXME RISCV: check usage *)
  "\<lbrace>\<lambda>s. obj_at (empty_table S) word s\<rbrace>
    store_pte xa InvalidPTE
   \<lbrace>\<lambda>rv s. obj_at (empty_table S) word s\<rbrace>"
  apply (wp get_object_wp | simp add: store_pte_def set_pt_def set_object_def)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma unmap_page_table_empty: (* FIXME RISCV: check usage *)
  "\<lbrace>\<lambda>s. obj_at (empty_table S) word s\<rbrace>
    unmap_page_table aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table S) word s\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp store_pte_unmap_empty | simp | wpc)+
  done

definition
  replaceable_or_arch_update
where
  "replaceable_or_arch_update \<equiv> \<lambda>s slot cap cap'.
   if is_frame_cap cap
   then is_arch_update cap cap' \<and>
        (\<forall>asid vref. vs_cap_ref cap' = Some (asid,vref) \<longrightarrow>
           vs_cap_ref cap = Some (asid,vref) \<and>
           obj_refs cap = obj_refs cap' \<or>
           (\<forall>oref\<in>obj_refs cap'. \<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, oref)))
   else replaceable s slot cap cap'"

lemma is_final_cap_pt_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def gen_obj_refs_def)
  done

lemma is_final_cap_pd_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  by (rule is_final_cap_pt_asid_eq)

lemma cte_wp_at_obj_refs_singleton_page_table:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma final_cap_pt_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PageTableCap p asid)) s;
    cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid'))) slot s;
    cte_wp_at ((=) (ArchObjectCap (PageTableCap p asid''))) slot' s\<rbrakk> \<Longrightarrow>
   slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: gen_obj_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma is_arch_update_reset_page:
  "is_arch_update
     (ArchObjectCap (FrameCap p r sz dev m))
     (ArchObjectCap (FrameCap p r' sz dev m'))"
  apply (simp add: is_arch_update_def is_arch_cap_def cap_master_cap_def)
  done

crunch caps_of_state [wp]: arch_finalise_cap "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps simp: crunch_simps)

lemma set_vm_root_empty[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (empty_table S) p s)\<rbrace> set_vm_root v \<lbrace>\<lambda>_ s. P (obj_at (empty_table S) p s) \<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wpsimp wp: get_cap_wp)
  done

lemma set_asid_pool_empty[wp]:
  "\<lbrace>obj_at (empty_table S) word\<rbrace> set_asid_pool x2 pool' \<lbrace>\<lambda>xb. obj_at (empty_table S) word\<rbrace>"
  by (wpsimp wp: set_object_wp simp: set_asid_pool_def obj_at_def empty_table_def)

lemma delete_asid_empty_table_pt[wp]:
  "delete_asid a word \<lbrace>\<lambda>s. obj_at (empty_table S) word s\<rbrace>"
   apply (simp add: delete_asid_def)
   apply wpsimp
   done

lemma ucast_less_shiftl_helper3:
  "\<lbrakk> len_of TYPE('b) + 3 < len_of TYPE('a); 2 ^ (len_of TYPE('b) + 3) \<le> n\<rbrakk>
    \<Longrightarrow> (ucast (x :: 'b::len word) << 3) < (n :: 'a::len word)"
  apply (erule order_less_le_trans[rotated])
  using ucast_less[where x=x and 'a='a]
  apply (simp only: shiftl_t2n field_simps)
  apply (rule word_less_power_trans2; simp)
  done

lemma caps_of_state_aligned_page_table:
  "\<lbrakk>caps_of_state s slot = Some (ArchObjectCap (PageTableCap word option)); invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pt_bits_def pageBits_def)
  done

end

lemma invs_valid_arch_capsI:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (simp add: invs_def valid_state_def)

context Arch begin global_naming RISCV64 (*FIXME: arch_split*)

lemma arch_finalise_pt_empty:
  "\<lbrace>(\<lambda>s. obj_at (empty_table {}) ptr s) and valid_cap (ArchObjectCap acap) and
    K (is_pt_cap (ArchObjectCap acap) \<and> aobj_ref acap = Some ptr)\<rbrace>
  arch_finalise_cap acap final
  \<lbrace>\<lambda>rv s. obj_at (empty_table {}) ptr s\<rbrace>"
  by (rule hoare_gen_asm)
     (wpsimp simp: is_cap_simps arch_finalise_cap_def wp: unmap_page_table_empty)

lemma do_machine_op_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. P (reachable_frame_cap cap s)\<rbrace>
   do_machine_op mo
   \<lbrace>\<lambda>rv s. P (reachable_frame_cap cap s)\<rbrace>"
  apply (simp add:reachable_frame_cap_def reachable_target_def)
  apply (wp_pre, wps dmo.vs_lookup_pages, wpsimp)
  apply simp
  done

lemma replaceable_or_arch_update_pg:
  " (case (vs_cap_ref (ArchObjectCap (FrameCap word fun vm_pgsz dev y))) of None \<Rightarrow> True | Some (asid,vref) \<Rightarrow>
     \<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, word))
  \<longrightarrow> replaceable_or_arch_update s slot (ArchObjectCap (FrameCap word fun vm_pgsz dev None))
                (ArchObjectCap (FrameCap word fun vm_pgsz dev y))"
  unfolding replaceable_or_arch_update_def
  apply (auto simp: is_cap_simps is_arch_update_def cap_master_cap_simps)
  done


global_naming Arch

crunch invs[wp]: prepare_thread_delete invs
  (ignore: set_object)

lemma (* finalise_cap_invs *)[Finalise_AI_asms]:
  shows "\<lbrace>invs and cte_wp_at ((=) cap) slot\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
         apply (wp cancel_all_ipc_invs cancel_all_signals_invs unbind_notification_invs
                   unbind_maybe_notification_invs
                  | simp add: o_def split del: if_split cong: if_cong
                  | wpc )+
      apply clarsimp (* thread *)
      apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
      apply (clarsimp simp: valid_cap_def)
      apply (frule(1) valid_global_refsD[OF invs_valid_global_refs])
       apply (simp add: global_refs_def, rule disjI1, rule refl)
      apply (simp add: cap_range_def)
     apply (wp deleting_irq_handler_invs  | simp | intro conjI impI)+
  apply (auto dest: cte_wp_at_valid_objs_valid_cap)
  done

lemma (* finalise_cap_irq_node *)[Finalise_AI_asms]:
"\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> finalise_cap a b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp | clarsimp)+
  done

lemmas (*arch_finalise_cte_irq_node *) [wp,Finalise_AI_asms]
    = hoare_use_eq_irq_node [OF arch_finalise_cap_irq_node arch_finalise_cap_cte_wp_at]

lemma (* deleting_irq_handler_st_tcb_at *) [Finalise_AI_asms]:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma irq_node_global_refs_ARCH [Finalise_AI_asms]:
  "interrupt_irq_node s irq \<in> global_refs s"
  by (simp add: global_refs_def)

lemma (* get_irq_slot_fast_finalisable *)[wp,Finalise_AI_asms]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>cte_wp_at can_fast_finalise\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def)
  apply (drule spec[where x=irq], drule cap_table_at_cte_at[where offset="[]"])
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (case_tac "cap = cap.NullCap")
   apply (simp add: can_fast_finalise_def)
  apply (frule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
   apply simp
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (drule(1) valid_global_refsD [OF _ _ irq_node_global_refs_ARCH[where irq=irq]])
  apply (case_tac c, simp_all)
     apply (clarsimp simp: cap_range_def)
    apply (clarsimp simp: cap_range_def)
   apply (clarsimp simp: appropriate_cte_cap_def can_fast_finalise_def split: cap.split_asm)
  apply (clarsimp simp: cap_range_def)
  done

lemma (* replaceable_or_arch_update_same *) [Finalise_AI_asms]:
  "replaceable_or_arch_update s slot cap cap"
  by (clarsimp simp: replaceable_or_arch_update_def
                replaceable_def is_arch_update_def is_cap_simps)

lemma (* replace_cap_invs_arch_update *)[Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. cte_wp_at (replaceable_or_arch_update s p cap) p s
        \<and> invs s
        \<and> cap \<noteq> cap.NullCap
        \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
        \<and> s \<turnstile> cap\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (simp add:replaceable_or_arch_update_def)
  apply (cases "is_frame_cap cap")
   apply (wp hoare_pre_disj[OF arch_update_cap_invs_unmap_page arch_update_cap_invs_map])
   apply (simp add:replaceable_or_arch_update_def replaceable_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps gen_obj_refs_def
                         cap_master_cap_simps is_arch_update_def)
  apply (wp replace_cap_invs)
  apply simp
  done

lemma dmo_pred_tcb_at[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (pred_tcb_at f Q t s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma dmo_tcb_cap_valid_ARCH [Finalise_AI_asms]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  apply (simp add: tcb_cap_valid_def no_cap_to_obj_with_diff_ref_def)
  apply (wp_pre, wps, rule hoare_vcg_prop)
  apply simp
  done

lemma dmo_vs_lookup_target[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (vs_lookup_target level asid vref s)\<rbrace>"
  by (rule dmo.vs_lookup_pages)

lemma dmo_reachable_target[wp]:
  "do_machine_op mop \<lbrace>\<lambda>s. P (reachable_target ref p s)\<rbrace>"
  apply (simp add: reachable_target_def split_def)
  apply (wp_pre, wps, wp)
  apply simp
  done

lemma (* dmo_replaceable_or_arch_update *) [Finalise_AI_asms,wp]:
  "\<lbrace>\<lambda>s. replaceable_or_arch_update s slot cap cap'\<rbrace>
    do_machine_op mo
  \<lbrace>\<lambda>r s. replaceable_or_arch_update s slot cap cap'\<rbrace>"
  unfolding replaceable_or_arch_update_def replaceable_def no_cap_to_obj_with_diff_ref_def
            replaceable_final_arch_cap_def replaceable_non_final_arch_cap_def
  apply (wp_pre, wps dmo_tcb_cap_valid_ARCH do_machine_op_reachable_pg_cap)
   apply (rule hoare_vcg_prop)
  apply simp
  done

end

context begin interpretation Arch .
requalify_consts replaceable_or_arch_update
end

interpretation Finalise_AI_3?: Finalise_AI_3
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming RISCV64

lemma typ_at_data_at_wp:
  assumes typ_wp: "\<And>a.\<lbrace>typ_at a p \<rbrace> g \<lbrace>\<lambda>s. typ_at a p\<rbrace>"
  shows "\<lbrace>data_at b p\<rbrace> g \<lbrace>\<lambda>s. data_at b p\<rbrace>"
  apply (simp add: data_at_def)
  apply (wp typ_wp hoare_vcg_disj_lift)
  done

end

interpretation Finalise_AI_4?: Finalise_AI_4
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming RISCV64

lemma set_asid_pool_obj_at_ptr:
  "\<lbrace>\<lambda>s. P (ArchObj (arch_kernel_obj.ASIDPool mp))\<rbrace>
     set_asid_pool ptr mp
   \<lbrace>\<lambda>rv s. obj_at P ptr s\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

locale_abbrev
  "asid_table_update asid ap s \<equiv>
     s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>"

lemma valid_table_caps_table [simp]:
  "valid_table_caps (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := table'\<rparr>\<rparr>) = valid_table_caps s"
  by (simp add: valid_table_caps_def)

lemma valid_kernel_mappings [iff]:
  "valid_kernel_mappings (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := table'\<rparr>\<rparr>) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)

crunches unmap_page_table, store_pte, delete_asid_pool, copy_global_mappings
  for valid_cap[wp]: "valid_cap c"
  (wp: mapM_wp_inv mapM_x_wp' simp: crunch_simps)

lemmas delete_asid_typ_ats[wp] = abs_typ_at_lifts [OF delete_asid_typ_at]

lemma arch_finalise_cap_valid_cap[wp]:
  "arch_finalise_cap cap b \<lbrace>valid_cap c\<rbrace>"
  unfolding arch_finalise_cap_def
  by (wpsimp split: arch_cap.split option.split bool.split)

global_naming Arch

lemmas clearMemory_invs[wp,Finalise_AI_asms] = clearMemory_invs

lemma valid_idle_has_null_cap_ARCH[Finalise_AI_asms]:
  "\<lbrakk> if_unsafe_then_cap s; valid_global_refs s; valid_idle s; valid_irq_node s;
    caps_of_state s (idle_thread s, v) = Some cap \<rbrakk>
   \<Longrightarrow> cap = NullCap"
  apply (rule ccontr)
  apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (case_tac capa, simp_all add: cap_range_def global_refs_def)[1]
  apply (clarsimp simp: valid_irq_node_def valid_idle_def pred_tcb_at_def
                        obj_at_def is_cap_table_def)
  apply (rename_tac word tcb)
  apply (drule_tac x=word in spec, simp)
  done

lemma (* zombie_cap_two_nonidles *)[Finalise_AI_asms]:
  "\<lbrakk> caps_of_state s ptr = Some (Zombie ptr' zbits n); invs s \<rbrakk>
       \<Longrightarrow> fst ptr \<noteq> idle_thread s \<and> ptr' \<noteq> idle_thread s"
  apply (frule valid_global_refsD2, clarsimp+)
  apply (simp add: cap_range_def global_refs_def)
  apply (cases ptr, auto dest: valid_idle_has_null_cap_ARCH[rotated -1])[1]
  done

crunches empty_slot, finalise_cap, send_ipc, receive_ipc
  for ioports[wp]: valid_ioports
  (wp: crunch_wps valid_ioports_lift simp: crunch_simps ignore: set_object)

lemma arch_derive_cap_notzombie[wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap acap \<lbrace>\<lambda>rv s. \<not> is_zombie rv\<rbrace>, -"
  by (cases acap; wpsimp simp: arch_derive_cap_def is_zombie_def o_def)

lemma arch_derive_cap_notIRQ[wp]:
  "\<lbrace>\<top>\<rbrace> arch_derive_cap cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.IRQControlCap\<rbrace>,-"
  by (cases cap; wpsimp simp: arch_derive_cap_def o_def)

end

interpretation Finalise_AI_5?: Finalise_AI_5
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

end
