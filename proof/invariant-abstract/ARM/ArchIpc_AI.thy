(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchIpc_AI
imports "../Ipc_AI"
begin

context Arch begin global_naming ARM

named_theorems Ipc_AI_assms

crunch pspace_respects_device_region[wp]: set_extra_badge "pspace_respects_device_region"

crunch cap_refs_respects_device_region[wp]: set_extra_badge "cap_refs_respects_device_region"
  (wp: crunch_wps cap_refs_respects_device_region_dmo)

lemma update_cap_data_closedform:
  "update_cap_data pres w cap =
   (case cap of
     cap.EndpointCap r badge rights \<Rightarrow>
       if badge = 0 \<and> \<not> pres then (cap.EndpointCap r (w && mask 28) rights) else cap.NullCap
   | cap.NotificationCap r badge rights \<Rightarrow>
       if badge = 0 \<and> \<not> pres then (cap.NotificationCap r (w && mask 28) rights) else cap.NullCap
   | cap.CNodeCap r bits guard \<Rightarrow>
       if word_bits < unat ((w >> 3) && mask 5) + bits
       then cap.NullCap
       else cap.CNodeCap r bits ((\<lambda>g''. drop (size g'' - unat ((w >> 3) && mask 5)) (to_bl g'')) ((w >> 8) && mask 18))
   | cap.ThreadCap r \<Rightarrow> cap.ThreadCap r
   | cap.DomainCap \<Rightarrow> cap.DomainCap
   | cap.UntypedCap d p n idx \<Rightarrow> cap.UntypedCap d p n idx
   | cap.NullCap \<Rightarrow> cap.NullCap
   | cap.ReplyCap t \<Rightarrow> cap.ReplyCap t
   | cap.SchedContextCap s n \<Rightarrow> cap.SchedContextCap s n
   | cap.SchedControlCap \<Rightarrow> cap.SchedControlCap
   | cap.IRQControlCap \<Rightarrow> cap.IRQControlCap
   | cap.IRQHandlerCap irq \<Rightarrow> cap.IRQHandlerCap irq
   | cap.Zombie r b n \<Rightarrow> cap.Zombie r b n
   | cap.ArchObjectCap cap \<Rightarrow> cap.ArchObjectCap cap)"
  apply (cases cap,
         simp_all only: cap.simps update_cap_data_def is_ep_cap.simps if_False if_True
                        is_ntfn_cap.simps is_cnode_cap.simps is_arch_cap_def word_size
                        cap_ep_badge.simps badge_update_def o_def cap_rights_update_def
                        simp_thms cap_rights.simps Let_def split_def
                        the_cnode_cap_def fst_conv snd_conv fun_app_def the_arch_cap_def
                        arch_update_cap_data_def
                  cong: if_cong)
  apply (auto simp: word_bits_def)
  done

lemma cap_asid_PageCap_None [simp]:
  "cap_asid (ArchObjectCap (PageCap dev r R pgsz None)) = None"
  by (simp add: cap_asid_def)

lemma arch_derive_cap_is_derived:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap . cap_master_cap cap =
                          cap_master_cap (ArchObjectCap c') \<and>
                          cap_aligned cap \<and>
                          cap_asid cap = cap_asid (ArchObjectCap c') \<and>
                          vs_cap_ref cap = vs_cap_ref (ArchObjectCap c')) p s\<rbrace>
     arch_derive_cap c'
   \<lbrace>\<lambda>rv s. cte_wp_at (is_derived (cdt s) p (ArchObjectCap rv)) p s\<rbrace>, -"
  unfolding arch_derive_cap_def
  apply(cases c', simp_all add: is_cap_simps cap_master_cap_def)
      apply((wp throwError_validE_R
             | clarsimp simp: is_derived_def
                              is_cap_simps cap_master_cap_def
                              cap_aligned_def is_aligned_no_overflow is_pt_cap_def
                              cap_asid_def vs_cap_ref_def
             | erule cte_wp_at_weakenE
             | simp split: arch_cap.split_asm cap.split_asm option.splits
             | rule conjI)+)
  done

lemma derive_cap_is_derived [Ipc_AI_assms]:
  "\<lbrace>\<lambda>s. c'\<noteq> cap.NullCap \<longrightarrow> cte_wp_at (\<lambda>cap. cap_master_cap cap = cap_master_cap c'
                     \<and> (cap_badge cap, cap_badge c') \<in> capBadge_ordering False
                     \<and> cap_asid cap = cap_asid c'
                     \<and> vs_cap_ref cap = vs_cap_ref c') slot s
       \<and> valid_objs s\<rbrace>
  derive_cap slot c'
  \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) slot rv) slot s\<rbrace>, -"
  unfolding derive_cap_def
  apply (cases c', simp_all add: is_cap_simps)
          apply ((wp ensure_no_children_wp
                    | clarsimp simp: is_derived_def is_cap_simps
                                     cap_master_cap_def bits_of_def
                                     same_object_as_def is_pt_cap_def
                                     cap_asid_def
                    | fold validE_R_def
                    | erule cte_wp_at_weakenE
                    | simp split: cap.split_asm)+)[11]
(*  apply(wp, simp add: o_def)
  apply(wp hoare_drop_imps arch_derive_cap_is_derived)
  apply(clarify, drule cte_wp_at_eqD, clarify)
  apply(frule(1) cte_wp_at_valid_objs_valid_cap)
  apply(erule cte_wp_at_weakenE)
  apply(clarsimp simp: valid_cap_def)
  done *) sorry

lemma is_derived_cap_rights [simp, Ipc_AI_assms]:
  "is_derived m p (cap_rights_update R c) = is_derived m p c"
  apply (rule ext)
  apply (simp add: cap_rights_update_def is_derived_def is_cap_simps)
  apply (case_tac x, simp_all)
           apply (simp add: cap_master_cap_def bits_of_def is_cap_simps
                             vs_cap_ref_def
                     split: cap.split)+
  apply (simp add: is_cap_simps is_page_cap_def
             cong: arch_cap.case_cong)
  apply (simp split: arch_cap.split cap.split
                add: is_cap_simps acap_rights_update_def is_pt_cap_def)
  done

lemma data_to_message_info_valid [Ipc_AI_assms]:
  "valid_message_info (data_to_message_info w)"
  apply (simp add: valid_message_info_def data_to_message_info_def)
  apply (rule conjI)
   apply (simp add: word_and_le1 msg_max_length_def msg_max_extra_caps_def Let_def not_less)+
  apply (subgoal_tac "(w >> 7) && 3 \<le> 3")
   apply (subgoal_tac "(3 :: 32 word) \<le> 7")
    apply (clarsimp simp: order.trans)
   apply simp
  apply (clarsimp simp: word_and_le1)
  done

lemma get_extra_cptrs_length[wp, Ipc_AI_assms]:
  "\<lbrace>\<lambda>s . valid_message_info mi\<rbrace>
   get_extra_cptrs buf mi
   \<lbrace>\<lambda>rv s. length rv \<le> msg_max_extra_caps\<rbrace>"
  apply (cases buf)
   apply (simp, wp, simp)
  apply (simp add: msg_max_length_def)
  apply (subst hoare_liftM_subst, simp add: o_def)
  apply (rule hoare_pre)
   apply (rule mapM_length, simp)
  apply (clarsimp simp: valid_message_info_def msg_max_extra_caps_def
                        word_le_nat_alt
                 intro: length_upt)
  done

lemma cap_asid_rights_update [simp, Ipc_AI_assms]:
  "cap_asid (cap_rights_update R c) = cap_asid c"
  apply (simp add: cap_rights_update_def acap_rights_update_def split: cap.splits arch_cap.splits)
  apply (clarsimp simp: cap_asid_def)
  done

lemma cap_rights_update_vs_cap_ref[simp, Ipc_AI_assms]:
  "vs_cap_ref (cap_rights_update rs cap) = vs_cap_ref cap"
  by (simp add: vs_cap_ref_def cap_rights_update_def
                acap_rights_update_def
         split: cap.split arch_cap.split)

lemma is_derived_cap_rights2[simp, Ipc_AI_assms]:
  "is_derived m p c (cap_rights_update R c') = is_derived m p c c'"
  apply (case_tac c')
  apply (simp_all add: cap_rights_update_def)
  apply (clarsimp simp: is_derived_def is_cap_simps cap_master_cap_def vs_cap_ref_def
                 split: cap.splits )+
  apply (rename_tac acap1 acap2)
  apply (case_tac acap1)
   by (auto simp: acap_rights_update_def)

lemma cap_range_update [simp, Ipc_AI_assms]:
  "cap_range (cap_rights_update R cap) = cap_range cap"
  by (simp add: cap_range_def cap_rights_update_def acap_rights_update_def
         split: cap.splits arch_cap.splits)

lemma derive_cap_idle[wp, Ipc_AI_assms]:
  "\<lbrace>\<lambda>s. global_refs s \<inter> cap_range cap = {}\<rbrace>
   derive_cap slot cap
  \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>, -"
  apply (simp add: derive_cap_def)
  apply (rule hoare_pre)
   apply (wpc| wp | simp add: arch_derive_cap_def)+
  apply (case_tac cap, simp_all add: cap_range_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp_all)
  done

lemma arch_derive_cap_objrefs_iszombie [Ipc_AI_assms]:
  "\<lbrace>\<lambda>s . P (set_option (aobj_ref cap)) False s\<rbrace>
     arch_derive_cap cap
   \<lbrace>\<lambda>rv s. P (set_option (aobj_ref rv)) False s\<rbrace>,-"
  apply(cases cap, simp_all add: is_zombie_def arch_derive_cap_def)
      apply(rule hoare_pre, wpc?, wp+, simp)+
  done

lemma obj_refs_remove_rights[simp, Ipc_AI_assms]:
  "obj_refs (remove_rights rs cap) = obj_refs cap"
  by (simp add: remove_rights_def cap_rights_update_def
                acap_rights_update_def
         split: cap.splits arch_cap.splits)

lemma storeWord_um_inv:
  "\<lbrace>\<lambda>s. underlying_memory s = um\<rbrace>
   storeWord a v
   \<lbrace>\<lambda>_ s. is_aligned a 2 \<and> x \<in> {a,a+1,a+2,a+3} \<or> underlying_memory s x = um x\<rbrace>"
  apply (simp add: storeWord_def is_aligned_mask)
  apply wp
  apply simp
  done

lemma store_word_offs_vms[wp, Ipc_AI_assms]:
  "\<lbrace>valid_machine_state\<rbrace> store_word_offs ptr offs v \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>(l::word32) (p::word32) sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l p sz
    assume al: "(p::word32) && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBitsForSize sz" by (case_tac sz, simp_all)
    show "?thesis l p sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed

  show ?thesis
    apply (simp add: valid_machine_state_def store_word_offs_def
                     do_machine_op_def split_def)
    apply wp
    apply clarsimp
    apply (drule_tac use_valid)
    apply (rule_tac x=p in storeWord_um_inv, simp+)
    apply (drule_tac x=p in spec)
    apply (erule disjE, simp)
    apply (erule disjE, simp_all)
    apply (erule conjE)
    apply (erule disjE, simp)
    apply (simp add: in_user_frame_def word_size_def)
    apply (erule exEI)
    apply (subgoal_tac "(ptr + of_nat offs * 4) && ~~ mask (pageBitsForSize x) =
                        p && ~~ mask (pageBitsForSize x)", simp)
    apply (simp only: is_aligned_mask[of _ 2])
    apply (elim disjE, simp_all)
    apply (rule aligned_offset_ignore[symmetric], simp+)+
    done
qed

lemma is_zombie_update_cap_data[simp, Ipc_AI_assms]:
  "is_zombie (update_cap_data P data cap) = is_zombie cap"
  by (simp add: update_cap_data_closedform is_zombie_def
         split: cap.splits)

lemma valid_msg_length_strengthen [Ipc_AI_assms]:
  "valid_message_info mi \<longrightarrow> unat (mi_length mi) \<le> msg_max_length"
  apply (clarsimp simp: valid_message_info_def)
  apply (subgoal_tac "unat (mi_length mi) \<le> unat (of_nat msg_max_length :: word32)")
   apply (clarsimp simp: unat_of_nat msg_max_length_def)
  apply (clarsimp simp: un_ui_le word_le_def)
  done

lemma copy_mrs_in_user_frame[wp, Ipc_AI_assms]:
  "\<lbrace>in_user_frame p\<rbrace> copy_mrs t buf t' buf' n \<lbrace>\<lambda>rv. in_user_frame p\<rbrace>"
  by (simp add: in_user_frame_def) (wp hoare_vcg_ex_lift)

lemma get_register_eq : "getRegister r = get_register r"
  apply (simp add: getRegister_def get_register_def)
  done

lemma as_user_getRestart_invs[wp]: "\<lbrace>P\<rbrace> as_user t getRestartPC \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: get_register_eq getRestartPC_def ; rule user_getreg_inv)
  done

lemma make_arch_fault_msg_inv[wp]: "\<lbrace>P\<rbrace> make_arch_fault_msg f t \<lbrace>\<lambda>_. P\<rbrace>"
  apply (cases f)
  apply simp
  apply wp
  done

lemma make_fault_message_inv[wp, Ipc_AI_assms]:
  "\<lbrace>P\<rbrace> make_fault_msg ft t \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases ft, simp_all split del: if_split)
     apply (wp as_user_inv getRestartPC_inv mapM_wp'
              | simp add: getRegister_def)+
  sorry

lemma do_fault_transfer_invs[wp, Ipc_AI_assms]:
  "\<lbrace>invs and tcb_at receiver\<rbrace>
      do_fault_transfer badge sender receiver recv_buf
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: do_fault_transfer_def split_def | wp
    | clarsimp split: option.split)+

lemma lookup_ipc_buffer_in_user_frame[wp, Ipc_AI_assms]:
  "\<lbrace>valid_objs and tcb_at t\<rbrace> lookup_ipc_buffer b t
   \<lbrace>case_option (\<lambda>_. True) in_user_frame\<rbrace>"
  apply (simp add: lookup_ipc_buffer_def)
  apply (wp get_cap_wp thread_get_wp | wpc | simp)+
  apply (clarsimp simp add: obj_at_def is_tcb)
  apply (rename_tac dev p R sz m)
  apply (subgoal_tac "in_user_frame (p + (tcb_ipc_buffer tcb &&
                                           mask (pageBitsForSize sz))) s", simp)
  apply (frule (1) cte_wp_valid_cap)
  apply (clarsimp simp add: valid_cap_def cap_aligned_def in_user_frame_def)
  apply (thin_tac "case_option a b c" for a b c)
  apply (rule_tac x=sz in exI)
  apply (subst is_aligned_add_helper[THEN conjunct2])
   apply simp
  apply (simp add: and_mask_less' word_bits_def)
  apply (clarsimp simp: caps_of_state_cteD'[where P = "\<lambda>x. True",simplified,symmetric])
  apply (drule(1) CSpace_AI.tcb_cap_slot_regular)
   apply simp
  apply (simp add: is_nondevice_page_cap_def is_nondevice_page_cap_arch_def case_bool_If
            split: if_splits)
  done

lemma transfer_caps_loop_cte_wp_at:
  assumes imp: "\<And>cap. P cap \<Longrightarrow> \<not> is_untyped_cap cap"
  shows "\<lbrace>cte_wp_at P sl and K (sl \<notin> set slots) and (\<lambda>s. \<forall>x \<in> set slots. cte_at x s)\<rbrace>
   transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>rv. cte_wp_at P sl\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp split del: if_split)+
      apply (wp hoare_vcg_conj_lift cap_insert_weak_cte_wp_at2)
       apply (erule imp)
      apply (wp hoare_vcg_ball_lift
             | clarsimp simp: is_cap_simps split del:if_split
             | unfold derive_cap_def arch_derive_cap_def
             | wpc
             | rule conjI
             | case_tac slots)+
  done

lemma transfer_caps_tcb_caps:
  fixes P t ref mi caps ep receiver recv_buf
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: transfer_caps_def)
  apply (wp hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift
            transfer_caps_loop_cte_wp_at
         | wpc | simp)+
  apply (erule imp)
  apply (wp hoare_vcg_conj_lift hoare_vcg_const_imp_lift hoare_vcg_all_lift
            )
    apply (rule_tac Q = "\<lambda>rv s.  ( \<forall>x\<in>set rv. real_cte_at x s )
      \<and> cte_wp_at P (t, ref) s \<and> tcb_at t s"
       in hoare_strengthen_post)
     apply (wp get_rs_real_cte_at)
     apply clarsimp
     apply (drule(1) bspec)
     apply (clarsimp simp:obj_at_def is_tcb is_cap_table)
    apply (rule hoare_post_imp)
     apply (rule_tac Q="\<lambda>x. real_cte_at x s" in ballEI, assumption)
     apply (erule real_cte_at_cte)
    apply (rule get_rs_real_cte_at)
   apply clarsimp
 done

lemma transfer_caps_non_null_cte_wp_at:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding transfer_caps_def
  apply simp
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ball_lift transfer_caps_loop_cte_wp_at static_imp_wp
     | wpc | clarsimp simp:imp)+
   apply (rule hoare_strengthen_post
            [where Q="\<lambda>rv s'. (cte_wp_at (op \<noteq> cap.NullCap) ptr) s'
                      \<and> (\<forall>x\<in>set rv. cte_wp_at (op = cap.NullCap) x s')",
             rotated])
    apply (clarsimp)
    apply  (rule conjI)
     apply (erule contrapos_pn)
     apply (drule_tac x=ptr in bspec, assumption)
     apply (clarsimp elim!: cte_wp_at_orth)
    apply (rule ballI)
    apply (drule(1) bspec)
    apply (erule cte_wp_cte_at)
   apply (wp)
  apply (auto simp: cte_wp_at_caps_of_state)
  done

crunch cte_wp_at[wp,Ipc_AI_assms]: do_fault_transfer "cte_wp_at P p"

lemma do_normal_transfer_non_null_cte_wp_at [Ipc_AI_assms]:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>
   do_normal_transfer st send_buffer ep b gr rt recv_buffer
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding do_normal_transfer_def
  apply simp
  apply (wp transfer_caps_non_null_cte_wp_at
    | clarsimp simp:imp)+
  done

lemma do_normal_transfer_tcb_caps:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
   do_normal_transfer st sb ep badge grant rt rb
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_normal_transfer_def)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps transfer_caps_tcb_caps
     | simp add:imp)+
  done

lemma do_ipc_transfer_tcb_caps [Ipc_AI_assms]:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t\<rbrace>
   do_ipc_transfer st ep b gr rt
   \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  apply (simp add: do_ipc_transfer_def)
  apply (rule hoare_pre)
  apply (wp do_normal_transfer_tcb_caps hoare_drop_imps
       | wpc | simp add:imp)+
  done

lemma set_thread_state_valid_vso_at[wp]:
  "\<lbrace>valid_vso_at a\<rbrace> set_thread_state s st \<lbrace>\<lambda>rv. valid_vso_at a\<rbrace>"
  apply (clarsimp simp: valid_vso_at_def)
  by (wpsimp wp: sts_obj_at_impossible sts_typ_ats hoare_vcg_ex_lift)

lemma cap_insert_valid_vso_at[wp]:
  "\<lbrace>valid_vso_at a\<rbrace> cap_insert c sl sl' \<lbrace>\<lambda>rv. valid_vso_at a\<rbrace>"
  apply (clarsimp simp: valid_vso_at_def)
  by (wpsimp wp: sts_obj_at_impossible sts_typ_ats hoare_vcg_ex_lift)

crunch typ_at[Ipc_AI_assms]: handle_arch_fault_reply, arch_get_sanitise_register_info "P (typ_at T p s)"

lemma transfer_caps_loop_valid_vspace_objs[wp, Ipc_AI_assms]:
  "\<lbrace>valid_vspace_objs\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (induct caps arbitrary: slots n mi, simp)
  apply (clarsimp simp: Let_def split_def whenE_def
                  cong: if_cong list.case_cong
             split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift
              derive_cap_is_derived_foo
             hoare_drop_imps
        | assumption | simp split del: if_split)+
  done

crunch aligned                   [wp, Ipc_AI_assms]:  make_arch_fault_msg "pspace_aligned"
crunch distinct                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "pspace_distinct"
crunch vmdb                      [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_mdb"
crunch vmdb                      [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_mdb"
crunch ifunsafe                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "if_unsafe_then_cap"
crunch iflive                    [wp, Ipc_AI_assms]:  make_arch_fault_msg "if_live_then_nonz_cap"
crunch state_refs_of             [wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (state_refs_of s)"
crunch ct                        [wp, Ipc_AI_assms]:  make_arch_fault_msg "cur_tcb"
crunch zombies                   [wp, Ipc_AI_assms]:  make_arch_fault_msg "zombies_final"
crunch it                        [wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (idle_thread s)"
crunch valid_globals             [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_global_refs"
crunch reply_masters             [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_reply_masters"
crunch valid_idle                [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_idle"
crunch arch                      [wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (arch_state s)"
crunch typ_at                    [wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (typ_at T p s)"
crunch irq_node                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (interrupt_irq_node s)"
crunch valid_reply               [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_reply_caps"
crunch irq_handlers              [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_irq_handlers"
crunch vspace_objs               [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_vspace_objs"
crunch global_objs               [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_global_objs"
crunch global_vspace_mapping     [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_global_vspace_mappings"
crunch arch_caps                 [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_arch_caps"
crunch v_ker_map                 [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_kernel_mappings"
crunch eq_ker_map                [wp, Ipc_AI_assms]:  make_arch_fault_msg "equal_kernel_mappings"
crunch asid_map                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_asid_map"
crunch only_idle                 [wp, Ipc_AI_assms]:  make_arch_fault_msg "only_idle"
crunch pspace_in_kernel_window   [wp, Ipc_AI_assms]:  make_arch_fault_msg "pspace_in_kernel_window"
crunch cap_refs_in_kernel_window [wp, Ipc_AI_assms]:  make_arch_fault_msg "cap_refs_in_kernel_window"
crunch valid_objs                [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_objs"
crunch valid_ioc                 [wp, Ipc_AI_assms]:  make_arch_fault_msg "valid_ioc"
crunch pred_tcb                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "pred_tcb_at proj P t"
crunch cap_to                    [wp, Ipc_AI_assms]:  make_arch_fault_msg "ex_nonz_cap_to p"
crunch pred_tcb                  [wp, Ipc_AI_assms]:  make_arch_fault_msg "pred_tcb_at proj P t"
crunch invs                      [wp, Ipc_AI_assms]:  make_arch_fault_msg "invs"

crunch obj_at[wp, Ipc_AI_assms]:  make_arch_fault_msg "\<lambda>s. P (obj_at P' pd s)"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def)

crunch vms[wp, Ipc_AI_assms]: make_arch_fault_msg valid_machine_state
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

crunch valid_irq_states[wp, Ipc_AI_assms]: make_arch_fault_msg "valid_irq_states"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

crunch cap_refs_respects_device_region[wp, Ipc_AI_assms]: make_arch_fault_msg "cap_refs_respects_device_region"
  (wp: as_user_inv getRestartPC_inv mapM_wp'  simp: getRegister_def ignore: do_machine_op)

end

global_interpretation Ipc_AI?: Ipc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Ipc_AI_assms)?)
  qed

context Arch begin global_naming ARM

named_theorems Ipc_AI_cont_assms

crunch pspace_respects_device_region[wp, Ipc_AI_cont_assms]: do_ipc_transfer "pspace_respects_device_region"
  (wp: crunch_wps ignore: const_on_failure simp: crunch_simps)

lemma do_ipc_transfer_respects_device_region[Ipc_AI_cont_assms]:
  "\<lbrace>cap_refs_respects_device_region and tcb_at t and  valid_objs and valid_mdb\<rbrace>
   do_ipc_transfer t ep bg grt r
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  including no_pre
  apply (wpsimp simp: do_ipc_transfer_def do_normal_transfer_def transfer_caps_def bind_assoc
                  wp: hoare_vcg_all_lift hoare_drop_imps)+
         apply (subst ball_conj_distrib)
         apply (wpsimp wp: get_rs_cte_at2 thread_get_wp static_imp_wp grs_distinct
                           hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift
                     simp: obj_at_def is_tcb_def)+
  apply (simp split: kernel_object.split_asm)
  done

crunch state_hyp_refs_of[wp, Ipc_AI_cont_assms]: do_ipc_transfer "\<lambda> s. P (state_hyp_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM)

end

global_interpretation Ipc_AI_cont?: Ipc_AI_cont
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact Ipc_AI_cont_assms)?)
  qed

global_interpretation Ipc_AI_det?: Ipc_AI_det ..

end
