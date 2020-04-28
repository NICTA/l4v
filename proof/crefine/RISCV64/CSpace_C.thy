(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory CSpace_C
imports CSpaceAcc_C Machine_C
begin

context kernel_m
begin

lemma maskCapRights_cap_cases:
  "return (maskCapRights R c) =
  (case c of
    ArchObjectCap ac \<Rightarrow> return (Arch.maskCapRights R ac)
  | EndpointCap _ _ _ _ _ _ \<Rightarrow>
    return (capEPCanGrantReply_update (\<lambda>_. capEPCanGrantReply c \<and> capAllowGrantReply R)
             (capEPCanGrant_update (\<lambda>_. capEPCanGrant c \<and> capAllowGrant R)
               (capEPCanReceive_update (\<lambda>_. capEPCanReceive c \<and> capAllowRead R)
                 (capEPCanSend_update (\<lambda>_. capEPCanSend c \<and> capAllowWrite R) c))))
  | NotificationCap _ _ _ _ \<Rightarrow>
    return (capNtfnCanReceive_update
                        (\<lambda>_. capNtfnCanReceive c \<and> capAllowRead R)
                        (capNtfnCanSend_update
                          (\<lambda>_. capNtfnCanSend c \<and> capAllowWrite R) c))
  | ReplyCap _ _ _ \<Rightarrow>
    return (capReplyCanGrant_update
             (\<lambda>_. capReplyCanGrant c \<and> capAllowGrant R) c)
  | _ \<Rightarrow> return c)"
  apply (simp add: maskCapRights_def Let_def split del: if_split)
  apply (cases c; simp add: isCap_simps split del: if_split)
  done


(* FIXME x64: ucast? see how it goes *)
lemma wordFromVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call wordFromVMRights_'proc \<lbrace>\<acute>ret__unsigned_long = \<^bsup>s\<^esup>vm_rights\<rbrace>"
  by vcg simp?

(* FIXME x64: ucast? see how it goes *)
lemma vmRightsFromWord_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s} Call vmRightsFromWord_'proc \<lbrace>\<acute>ret__unsigned_long = \<^bsup>s\<^esup>w\<rbrace>"
  by vcg simp?

lemmas vmrights_defs =
  Kernel_C.VMReadOnly_def
  Kernel_C.VMKernelOnly_def
  Kernel_C.VMReadWrite_def

lemma maskVMRights_spec:
  "\<forall>s. \<Gamma> \<turnstile> ({s} \<inter>
           \<lbrace> \<acute>vm_rights && mask 2 = \<acute>vm_rights \<rbrace>)
  Call maskVMRights_'proc
  \<lbrace> vmrights_to_H \<acute>ret__unsigned_long =
    maskVMRights (vmrights_to_H \<^bsup>s\<^esup>vm_rights) (cap_rights_to_H (seL4_CapRights_lift \<^bsup>s\<^esup>cap_rights_mask)) \<and>
    \<acute>ret__unsigned_long && mask 2 = \<acute>ret__unsigned_long \<and>
    \<acute>ret__unsigned_long \<noteq> 0 \<rbrace>"
  apply vcg
  apply (clarsimp simp: vmrights_defs vmrights_to_H_def maskVMRights_def mask_def
                        cap_rights_to_H_def to_bool_def
                  split: bool.split)
  done

lemma frame_cap_rights [simp]:
  "cap_get_tag cap = scast cap_frame_cap
  \<Longrightarrow> cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap) && mask 2 =
     cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap)"
  apply (simp add: cap_frame_cap_lift_def)
  by (simp add: cap_lift_def cap_tag_defs mask_def word_bw_assocs)

lemma Arch_maskCapRights_ccorres [corres]:
  "ccorres ccap_relation ret__struct_cap_C_'
  \<top>
  (UNIV \<inter> \<lbrace>ccap_relation (ArchObjectCap arch_cap) \<acute>cap\<rbrace> \<inter>
  \<lbrace>ccap_rights_relation R \<acute>cap_rights_mask\<rbrace>)
  []
  (return (Arch.maskCapRights R arch_cap))
  (Call Arch_maskCapRights_'proc)"
  apply (cinit' lift: cap_' cap_rights_mask_')
   apply csymbr
   apply (unfold RISCV64_H.maskCapRights_def)
   apply (simp only: Let_def)
   apply (case_tac "cap_get_tag cap = scast cap_frame_cap")
    apply (clarsimp simp add: ccorres_cond_iffs cap_get_tag_isCap isCap_simps split del: if_splits)
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
    apply (clarsimp simp: return_def)
    apply (unfold ccap_relation_def)[1]
    apply (simp add: cap_frame_cap_lift [THEN iffD1])
    apply (clarsimp simp: cap_to_H_def)
    apply (simp add: map_option_case split: option.splits)
    apply (clarsimp simp: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
     apply (clarsimp simp: cap_frame_cap_lift_def)
     apply (clarsimp simp: ccap_rights_relation_def cap_frame_cap_lift c_valid_cap_def
                           cl_valid_cap_def mask_eq_iff word_less_alt
                    split: option.splits cap_CL.splits)
    apply (clarsimp simp: cap_frame_cap_lift_def)
    apply (clarsimp simp: ccap_rights_relation_def c_valid_cap_def cap_frame_cap_lift
                          cl_valid_cap_def mask_eq_iff word_less_alt)
   apply (clarsimp simp add: cap_get_tag_isCap isCap_simps simp del: not_ex)
   apply (rule ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp add: return_def simp del: not_ex)
   apply (cases arch_cap)
         by (fastforce simp add: cap_get_tag_isCap isCap_simps  simp del: not_ex omgwtfbbq)+

lemma to_bool_mask_to_bool_bf:
  "to_bool (x && mask (Suc 0)) = to_bool_bf (x::machine_word)"
  apply (simp add: to_bool_bf_def to_bool_def)
  apply (rule iffI)
   prefer 2
   apply simp
  apply (subgoal_tac "x && mask (Suc 0) < 2^(Suc 0)")
   apply simp
   apply (drule word_less_cases [where y=2])
   apply auto[1]
  apply (rule and_mask_less')
  apply simp
  done

lemma to_bool_cap_rights_bf:
  "to_bool (capAllowRead_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowRead_CL (seL4_CapRights_lift R))"
  "to_bool (capAllowWrite_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowWrite_CL (seL4_CapRights_lift R))"
  "to_bool (capAllowGrant_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowGrant_CL (seL4_CapRights_lift R))"
  "to_bool (capAllowGrantReply_CL (seL4_CapRights_lift R)) =
   to_bool_bf (capAllowGrantReply_CL (seL4_CapRights_lift R))"
  by (subst to_bool_bf_to_bool_mask,
      simp add: seL4_CapRights_lift_def mask_def word_bw_assocs, simp)+

lemma to_bool_ntfn_cap_bf:
  "cap_lift c = Some (Cap_notification_cap cap) \<Longrightarrow>
  to_bool (capNtfnCanSend_CL cap) = to_bool_bf (capNtfnCanSend_CL cap) \<and>
  to_bool (capNtfnCanReceive_CL cap) = to_bool_bf (capNtfnCanReceive_CL cap)"
  apply (simp add:cap_lift_def Let_def split: if_split_asm)
  apply (subst to_bool_bf_to_bool_mask,
         clarsimp simp: cap_lift_thread_cap mask_def word_bw_assocs)+
  apply simp
  done

lemma to_bool_reply_cap_bf:
  "cap_lift c = Some (Cap_reply_cap cap)
   \<Longrightarrow> to_bool (capReplyMaster_CL cap) = to_bool_bf (capReplyMaster_CL cap)
      \<and> to_bool (capReplyCanGrant_CL cap) = to_bool_bf (capReplyCanGrant_CL cap)"
  apply (simp add: cap_lift_def Let_def split: if_split_asm)
  apply (subst to_bool_bf_to_bool_mask,
         clarsimp simp: cap_lift_thread_cap mask_def word_bw_assocs)+
  apply simp
  done

lemma to_bool_ep_cap_bf:
  "cap_lift c = Some (Cap_endpoint_cap cap) \<Longrightarrow>
  to_bool (capCanSend_CL cap) = to_bool_bf (capCanSend_CL cap) \<and>
  to_bool (capCanReceive_CL cap) = to_bool_bf (capCanReceive_CL cap) \<and>
  to_bool (capCanGrant_CL cap) = to_bool_bf (capCanGrant_CL cap) \<and>
  to_bool (capCanGrantReply_CL cap) = to_bool_bf (capCanGrantReply_CL cap)"
  apply (simp add:cap_lift_def Let_def split: if_split_asm)
  apply (subst to_bool_bf_to_bool_mask,
         clarsimp simp: cap_lift_thread_cap mask_def word_bw_assocs)+
  apply simp
  done

lemma isArchCap_spec:
  "\<forall>s. \<Gamma>\<turnstile> {s} Call isArchCap_'proc \<lbrace>\<acute>ret__unsigned_long = from_bool (isArchCap_tag (cap_get_tag (cap_' s)))\<rbrace>"
  apply vcg
  apply (clarsimp simp: from_bool_def isArchCap_tag_def bool.split)
  apply (clarsimp simp: word_mod_2p_is_mask[where n=1, simplified] mask_def)
  apply word_bitwise
  done

lemma maskCapRights_ccorres [corres]:
  "ccorres ccap_relation ret__struct_cap_C_'
           \<top>
           (UNIV \<inter> \<lbrace>ccap_relation cap \<acute>cap\<rbrace> \<inter> \<lbrace>ccap_rights_relation R \<acute>cap_rights\<rbrace>)
           []
           (return (RetypeDecls_H.maskCapRights R cap)) (Call maskCapRights_'proc)"
  apply (cinit' lift: cap_' cap_rights_')
  apply csymbr
  apply (simp add: maskCapRights_cap_cases cap_get_tag_isCap del: Collect_const)
  apply wpc
              apply (simp add: Collect_const_mem from_bool_def)
              apply csymbr
              apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
              apply (simp add: ccorres_cond_iffs)
              apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
              apply (rule allI)
              apply (rule conseqPre)
               apply vcg
              apply clarsimp
              apply (simp add: cap_get_tag_isCap isCap_simps return_def)
             apply (simp add: Collect_const_mem from_bool_def)
             apply csymbr
             apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
             apply (simp add: ccorres_cond_iffs)
             apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
             apply (rule allI)
             apply (rule conseqPre)
              apply vcg
             apply (clarsimp simp: return_def)
            apply (simp add: Collect_const_mem from_bool_def)
            apply csymbr
            apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
            apply (simp add: ccorres_cond_iffs)
            apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
            apply (rule allI)
            apply (rule conseqPre)
             apply vcg
            apply clarsimp
            apply (simp add: cap_get_tag_isCap isCap_simps return_def)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply (rule imp_ignore)
            apply clarsimp
            apply (unfold ccap_relation_def)[1]
            apply (simp add: cap_notification_cap_lift [THEN iffD1])
            apply (clarsimp simp: cap_to_H_def)
            apply (simp add: map_option_case split: option.splits)
            apply (clarsimp simp add: cap_to_H_def Let_def
                               split: cap_CL.splits if_split_asm)
            apply (simp add: cap_notification_cap_lift_def)
            apply (simp add: ccap_rights_relation_def cap_rights_to_H_def
                             to_bool_ntfn_cap_bf
                             to_bool_mask_to_bool_bf to_bool_cap_rights_bf)
           apply (simp add: Collect_const_mem from_bool_def)
           apply csymbr
           apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
           apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
           apply (rule allI)
           apply (rule conseqPre)
            apply vcg
           apply (clarsimp simp: cap_get_tag_isCap isCap_simps return_def)
          apply (simp add: Collect_const_mem from_bool_def)
          apply csymbr
          apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
          apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
          apply (rule allI)
          apply (rule conseqPre)
           apply vcg
          apply clarsimp
          apply (simp add: cap_get_tag_isCap isCap_simps return_def)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply (rule imp_ignore)
          apply clarsimp
          apply (unfold ccap_relation_def)[1]
          apply (simp add: cap_endpoint_cap_lift [THEN iffD1])
          apply (clarsimp simp: cap_to_H_def)
          apply (simp add: map_option_case split: option.splits)
          apply (clarsimp simp add: cap_to_H_def Let_def
                             split: cap_CL.splits if_split_asm)
          apply (simp add: cap_endpoint_cap_lift_def)
          apply (simp add: ccap_rights_relation_def cap_rights_to_H_def
                           to_bool_ep_cap_bf
                           to_bool_mask_to_bool_bf to_bool_cap_rights_bf)
         apply (simp add: Collect_const_mem from_bool_def)
         apply csymbr
         apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
         apply (simp add: ccorres_cond_iffs)
         apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
         apply (rule allI)
         apply (rule conseqPre)
          apply vcg
         apply (clarsimp simp: return_def)
        apply (simp add: Collect_const_mem from_bool_def)
        apply csymbr
        apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs)
        apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
        apply (rule allI)
        apply (rule conseqPre)
         apply vcg
        apply (clarsimp simp: cap_get_tag_isCap isCap_simps return_def)
       apply (simp add: Collect_const_mem from_bool_def)
       apply (subst bind_return [symmetric])
       apply (rule ccorres_split_throws)
        apply ctac
          apply (rule_tac P=\<top> and P'="\<lbrace>\<acute>ret__struct_cap_C = ret__struct_cap_C\<rbrace>" in ccorres_inst)
          apply (rule ccorres_from_vcg_throws)
          apply (clarsimp simp: return_def)
          apply (rule conseqPre)
           apply vcg
          apply clarsimp
         apply wp
        apply vcg
       apply vcg
      apply (simp add: Collect_const_mem from_bool_def)
      apply csymbr
      apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
      apply ccorres_rewrite
      apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
      apply (rule allI)
      apply (rule conseqPre)
       apply vcg
      apply (simp add: cap_get_tag_isCap isCap_simps return_def)
      apply clarsimp
      apply (unfold ccap_relation_def)[1]
      apply (simp add: cap_reply_cap_lift [THEN iffD1])
      apply (clarsimp simp: cap_to_H_def)
      apply (simp add: map_option_case split: option.splits)
      apply (clarsimp simp add: cap_to_H_def Let_def
                      split: cap_CL.splits if_split_asm)
      apply (simp add: cap_reply_cap_lift_def)
      apply (simp add: ccap_rights_relation_def cap_rights_to_H_def
                       to_bool_reply_cap_bf
                       to_bool_mask_to_bool_bf to_bool_cap_rights_bf)
     apply (simp add: Collect_const_mem from_bool_def)
     apply csymbr
     apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
     apply (simp add: ccorres_cond_iffs)
     apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
     apply (rule allI)
     apply (rule conseqPre)
      apply vcg
     apply (clarsimp simp: return_def)
    apply (simp add: Collect_const_mem from_bool_def)
    apply csymbr
    apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
    apply (simp add: ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
    apply (rule allI)
    apply (rule conseqPre)
     apply vcg
    apply clarsimp
    apply (simp add: cap_get_tag_isCap isCap_simps return_def)
   apply (simp add: Collect_const_mem from_bool_def)
   apply csymbr
   apply (simp add: cap_get_tag_isCap isCap_simps del: Collect_const)
   apply (simp add: ccorres_cond_iffs)
   apply (rule ccorres_from_vcg_throws [where P=\<top> and P'=UNIV])
   apply (rule allI)
   apply (rule conseqPre)
    apply vcg
   apply (clarsimp simp: return_def)
  apply clarsimp
  done

abbreviation
  "lookupCap_xf \<equiv> liftxf errstate lookupCap_ret_C.status_C lookupCap_ret_C.cap_C ret__struct_lookupCap_ret_C_'"

lemma ccorres_return_cte_cteCap [corres]:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres ccap_relation xf
         (\<lambda>s. ctes_of s ptr = Some cte) {s. ptr_val (ptr' s) = ptr}  hs
         (return (cteCap cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s)))
           (Ptr &(ptr' s \<rightarrow>[''cap_C'']))) s))"
  apply (rule ccorres_return)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: xf_xfu ccap_relation_def)
  apply rule
  apply (erule r1)
  apply (drule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  apply (simp add: c_valid_cte_def)
done


lemma ccorres_return_cte_mdbnode [corres]:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres cmdbnode_relation xf
         (\<lambda>s. ctes_of s ptr = Some cte) {s. ptr_val (ptr' s) = ptr}  hs
         (return (cteMDBNode cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val (hrs_mem (t_hrs_' (globals s)))
           (Ptr &(ptr' s \<rightarrow>[''cteMDBNode_C'']))) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: return_def xf_xfu)
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  apply (erule r1)
  done


(* FIXME: MOVE *)
lemma heap_update_field_ext:
  "\<lbrakk>field_ti TYPE('a :: packed_type) f = Some t; c_guard p;
  export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
  \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f) :: 'b ptr) =
  (\<lambda>v hp. heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp)"
  apply (rule ext, rule ext)
  apply (erule (2) heap_update_field)
  done

lemma ccorres_updateCap [corres]:
  fixes ptr :: "cstate \<Rightarrow> cte_C ptr" and val :: "cstate \<Rightarrow> cap_C"
  shows "ccorres dc xfdc \<top>
        ({s. ccap_relation cap (val s)} \<inter> {s. ptr s = Ptr dest}) hs
        (updateCap dest cap)
        (Basic
  (\<lambda>s. globals_update
   (t_hrs_'_update
     (hrs_mem_update (heap_update (Ptr &(ptr s\<rightarrow>[''cap_C''])) (val s)))) s))"
  unfolding updateCap_def
  apply (cinitlift ptr)
  apply (erule ssubst)
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE)
  apply (rule_tac P = "\<lambda>s. ctes_of s dest = Some rva" in
    ccorres_from_vcg [where P' = "{s. ccap_relation cap (val s)}"])
  apply (rule allI)
  apply (rule conseqPre)
  apply vcg
  apply clarsimp
  apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def
     Let_def cpspace_relation_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
   apply (simp add:typ_heap_simps)
   apply (rule conjI)
    apply (erule (3) cpspace_cte_relation_upd_capI)
   apply (frule_tac f="ksPSpace" in arg_cong)
   apply (erule_tac t = s' in ssubst)
    apply simp
   apply (simp add: heap_to_user_data_def heap_to_device_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   by (auto simp: carch_state_relation_def cmachine_state_relation_def)

lemma ccorres_updateMDB_const [corres]:
  fixes ptr :: "cstate \<Rightarrow> cte_C ptr" and val :: "cstate \<Rightarrow> mdb_node_C"
  shows "ccorres dc xfdc (\<lambda>_. dest \<noteq> 0)
        ({s. cmdbnode_relation m (val s)} \<inter> {s. ptr s = Ptr dest}) hs
        (updateMDB dest (const m))
        (Basic
  (\<lambda>s. globals_update
   (t_hrs_'_update
     (hrs_mem_update (heap_update (Ptr &(ptr s\<rightarrow>[''cteMDBNode_C''])) (val s)))) s))"
  unfolding updateMDB_def
  apply (cinitlift ptr)
  apply (erule ssubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE)
  apply (rule_tac P = "\<lambda>s. ctes_of s dest = Some cte" in ccorres_from_vcg [where P' = "{s. cmdbnode_relation m (val s)}"])
  apply (rule allI)
  apply (rule conseqPre)
  apply vcg
  apply clarsimp
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
   apply (erule bexI [rotated])
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
     Let_def cpspace_relation_def
     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
   apply (rule conjI)
    apply (erule (3) cspace_cte_relation_upd_mdbI)
   apply (erule_tac t = s' in ssubst)
   apply (simp add: heap_to_user_data_def)
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   by (auto simp: carch_state_relation_def cmachine_state_relation_def)

(* 64 == badgeBits *)
lemma cap_lift_capNtfnBadge_mask_eq:
  "cap_lift cap = Some (Cap_notification_cap ec)
  \<Longrightarrow> capNtfnBadge_CL ec && mask 64 = capNtfnBadge_CL ec"
  unfolding cap_lift_def
  by (fastforce simp: Let_def mask_def word_bw_assocs split: if_split_asm)

lemma cap_lift_capEPBadge_mask_eq:
  "cap_lift cap = Some (Cap_endpoint_cap ec)
  \<Longrightarrow> capEPBadge_CL ec && mask 64 = capEPBadge_CL ec"
  unfolding cap_lift_def
  by (fastforce simp: Let_def mask_def word_bw_assocs split: if_split_asm)

lemma Arch_isCapRevocable_spec:
  "\<forall>s. \<Gamma>\<turnstile> {\<sigma>. s = \<sigma> \<and> True}
          Call Arch_isCapRevocable_'proc
        {t. \<forall>c c'.  ccap_relation c (derivedCap_' s) \<and> ccap_relation c' (srcCap_' s)
            \<longrightarrow> ret__unsigned_long_' t = from_bool (Arch.isCapRevocable c c')}"
  apply vcg
  by (auto simp: false_def from_bool_def RISCV64_H.isCapRevocable_def
                 cap_get_tag_isCap_unfolded_H_cap cap_tag_defs isCap_simps
                 cap_get_tag_isCap[unfolded, simplified]
          split: capability.splits arch_capability.splits bool.splits)

lemmas isCapRevocable_simps[simp] = Retype_H.isCapRevocable_def[split_simps capability.split]

context begin (* revokable_ccorres *)

private method revokable'_hammer = solves \<open>(
              simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def,
              rule ccorres_guard_imp,
              rule ccorres_return_C; clarsimp)\<close>

lemma revokable_ccorres:
  "ccorres (\<lambda>a c. from_bool a = c) ret__unsigned_long_'
           (\<lambda>_. capMasterCap cap = capMasterCap parent \<or> is_simple_cap' cap)
           (UNIV \<inter> {s. ccap_relation cap (derivedCap_' s)} \<inter> {s. ccap_relation parent (srcCap_' s)}) hs
           (return (isCapRevocable cap parent))
           (Call isCapRevocable_'proc)"
  apply (rule ccorres_gen_asm[where G=\<top>, simplified])
  apply (cinit' lift: derivedCap_' srcCap_')
   \<comment> \<open>Clear up Arch cap case\<close>
   apply csymbr
   apply (clarsimp simp: cap_get_tag_isCap split del: if_splits simp del: Collect_const)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_rhs_assoc)
    apply (clarsimp simp: isCap_simps)
    apply csymbr
    apply (drule spec, drule spec, drule mp, fastforce)
    apply ccorres_rewrite
    apply (drule sym, simp only:)
    apply (rule ccorres_return_C, clarsimp+)
  apply csymbr
  apply (rule_tac P'=UNIV and P=\<top> in ccorres_inst)
   apply (cases cap)
    \<comment> \<open>Uninteresting caps\<close>
              apply revokable'_hammer+
    \<comment> \<open>NotificationCap\<close>
            apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def)
            apply (rule ccorres_guard_imp, (rule ccorres_rhs_assoc)+, csymbr, csymbr)
              apply (rule ccorres_return_C, clarsimp+)
            apply (frule_tac cap'1=srcCap in cap_get_tag_NotificationCap[THEN iffD1])
             apply (clarsimp simp: cap_get_tag_isCap isCap_simps is_simple_cap'_def)
            apply (frule_tac cap'1=derivedCap in cap_get_tag_NotificationCap[THEN iffD1])
             apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
            apply (fastforce simp: cap_get_tag_isCap isCap_simps)
    \<comment> \<open>IRQHandlerCap\<close>
           apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def)
           apply (rule ccorres_guard_imp, csymbr)
             apply (rule ccorres_return_C, clarsimp+)
           apply (fastforce simp: cap_get_tag_isCap isCap_simps)
    \<comment> \<open>EndpointCap\<close>
          apply (simp add: cap_get_tag_isCap isCap_simps ccorres_cond_iffs from_bool_def true_def false_def)
          apply (rule ccorres_guard_imp, (rule ccorres_rhs_assoc)+, csymbr, csymbr)
            apply (rule ccorres_return_C, clarsimp+)
          apply (frule_tac cap'1=srcCap in cap_get_tag_EndpointCap[THEN iffD1])
           apply (clarsimp simp: cap_get_tag_isCap isCap_simps is_simple_cap'_def)
          apply (frule_tac cap'1=derivedCap in cap_get_tag_EndpointCap[THEN iffD1])
           apply (clarsimp simp: cap_get_tag_isCap isCap_simps)
          apply (fastforce simp: cap_get_tag_isCap isCap_simps)
    \<comment> \<open>Other Caps\<close>
  by (revokable'_hammer | fastforce simp: isCap_simps)+

end (* revokable_ccorres *)

lemma cteInsert_ccorres_mdb_helper:
  "\<lbrakk>cmdbnode_relation rva srcMDB; from_bool rvc = (newCapIsRevocable :: machine_word); srcSlot = Ptr src\<rbrakk>
       \<Longrightarrow> ccorres cmdbnode_relation newMDB_' (K (is_aligned src 3))
           UNIV hs
           (return
             (mdbFirstBadged_update (\<lambda>_. rvc)
               (mdbRevocable_update (\<lambda>_. rvc)
                 (mdbPrev_update (\<lambda>_. src) rva))))
           (\<acute>newMDB :== CALL mdb_node_set_mdbPrev(srcMDB,
            ptr_val srcSlot);;
            \<acute>newMDB :== CALL mdb_node_set_mdbRevocable(\<acute>newMDB,
            newCapIsRevocable);;
            \<acute>newMDB :== CALL mdb_node_set_mdbFirstBadged(\<acute>newMDB,
            newCapIsRevocable))"
  apply (rule ccorres_from_vcg)
  apply (rule allI)
  apply (rule conseqPre)
   apply vcg
  apply (clarsimp simp: return_def cmdbnode_relation_def mask_def)
  done

lemma ccorres_updateMDB_set_mdbNext [corres]:
  "src=src' \<Longrightarrow>
   ccorres dc xfdc ((\<lambda>_. src \<noteq> 0 \<and> is_aligned dest cteSizeBits \<and> canonical_address dest))
  ({s. mdb_node_ptr_' s = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])} \<inter>
   {s. v64_' s = dest}) []
  (updateMDB src (mdbNext_update (\<lambda>_. dest)))
  (Call mdb_node_ptr_set_mdbNext_'proc)"
  unfolding updateMDB_def
  apply (hypsubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_pre_getCTE
                 [where P = "\<lambda>cte s. ctes_of s src' = Some cte"
                    and P'= "\<lambda>_. (\<lbrace>\<acute>mdb_node_ptr = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])\<rbrace>
                                               \<inter> \<lbrace>\<acute>v64 = dest\<rbrace>)"])
   apply (rule ccorres_from_spec_modifies_heap)
       apply (rule mdb_node_ptr_set_mdbNext_spec)
      apply (rule mdb_node_ptr_set_mdbNext_modifies)
     apply simp
    apply clarsimp
    apply (rule rf_sr_cte_at_valid)
     apply simp
     apply (erule ctes_of_cte_at)
    apply assumption
   apply clarsimp
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI [rotated])
   apply (clarsimp simp: rf_sr_def cstate_relation_def
                         Let_def cpspace_relation_def cte_wp_at_ctes_of heap_to_user_data_def
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                         typ_heap_simps')
   apply (rule conjI)
    apply (erule (2) cspace_cte_relation_upd_mdbI)
    apply (simp add: cmdbnode_relation_def)
    apply (intro arg_cong[where f="\<lambda>f. mdbNext_update f mdb" for mdb] ext word_eqI)
    apply (simp add: sign_extend_bitwise_if' neg_mask_test_bit word_size)
    apply (match premises in C: "canonical_address _" and A: "is_aligned _ _" (multi) \<Rightarrow>
           \<open>match premises in H[thin]: _ (multi) \<Rightarrow> \<open>insert C A\<close>\<close>)
    apply (drule is_aligned_weaken[where y=2], simp add: objBits_defs)
    apply (case_tac "n < 2"; case_tac "n \<le> 38";
           clarsimp simp: linorder_not_less linorder_not_le is_aligned_nth[THEN iffD1])
    apply (fastforce simp: word_size dest: canonical_address_high_bits[simplified canonical_bit_def])
   apply (erule_tac t = s'a in ssubst)
   apply simp
   apply (rule conjI)
    apply (erule (1) setCTE_tcb_case)
   by (auto simp: carch_state_relation_def cmachine_state_relation_def)

lemma ccorres_updateMDB_set_mdbPrev [corres]:
  "src=src' \<Longrightarrow>
  ccorres dc xfdc (\<lambda>_. src \<noteq> 0 \<and> is_aligned dest cteSizeBits)
  ({s. mdb_node_ptr_' s = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])} \<inter>
   {s. v64_' s = dest}) []
  (updateMDB src (mdbPrev_update (\<lambda>_. dest)))
  (Call mdb_node_ptr_set_mdbPrev_'proc)"
  unfolding updateMDB_def
  apply (hypsubst)
  apply (rule ccorres_gen_asm [where G = \<top>, simplified])
  apply (simp only: Let_def)
  apply simp
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_pre_getCTE
                [where P = "\<lambda>cte s. ctes_of s src' = Some cte"
                   and P' = "\<lambda>_. (\<lbrace>\<acute>mdb_node_ptr = Ptr &((Ptr src' :: cte_C ptr)\<rightarrow>[''cteMDBNode_C''])\<rbrace>
                                    \<inter> \<lbrace>\<acute>v64 = dest\<rbrace>)"])
  apply (rule ccorres_from_spec_modifies_heap)
       apply (rule mdb_node_ptr_set_mdbPrev_spec)
      apply (rule mdb_node_ptr_set_mdbPrev_modifies)
     apply simp
    apply clarsimp
    apply (rule rf_sr_cte_at_valid)
     apply simp
     apply (erule ctes_of_cte_at)
    apply assumption
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp: typ_heap_simps)
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
   apply (erule bexI[rotated])
   apply (clarsimp simp: rf_sr_def cstate_relation_def
                         Let_def cpspace_relation_def cte_wp_at_ctes_of heap_to_user_data_def
                         cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                         typ_heap_simps')
   apply (rule conjI)
    apply (erule (2) cspace_cte_relation_upd_mdbI)
    apply (simp add: cmdbnode_relation_def mask_def)
   apply (erule_tac t = s'a in ssubst)
   apply (simp add: carch_state_relation_def cmachine_state_relation_def)
   apply (erule (1) setCTE_tcb_case)
  by clarsimp

lemma ccorres_updateMDB_skip:
  "ccorres dc xfdc (\<top> and (\<lambda>_. n = 0)) UNIV hs (updateMDB n f) SKIP"
  unfolding updateMDB_def
  apply (rule ccorres_gen_asm)
  apply simp
  apply (rule ccorres_return)
  apply simp
  apply vcg
  done

definition
  "is_simple_cap_tag (tag :: machine_word) \<equiv>
      tag \<noteq> scast cap_null_cap \<and> tag \<noteq> scast cap_irq_control_cap
    \<and> tag \<noteq> scast cap_untyped_cap \<and> tag \<noteq> scast cap_reply_cap
    \<and> tag \<noteq> scast cap_endpoint_cap \<and> tag \<noteq> scast cap_notification_cap
    \<and> tag \<noteq> scast cap_thread_cap \<and> tag \<noteq> scast cap_cnode_cap
    \<and> tag \<noteq> scast cap_zombie_cap \<and> tag \<noteq> scast cap_frame_cap"

(* Useful:
  apply (tactic {* let val _ = reset CtacImpl.trace_ceqv; val _ = reset CtacImpl.trace_ctac in all_tac end; *})
  *)
declare word_neq_0_conv [simp del]

schematic_goal ccap_relation_tag_Master:
  "\<And>ccap. \<lbrakk> ccap_relation cap ccap \<rbrakk>
      \<Longrightarrow> cap_get_tag ccap =
            case_capability ?a ?b ?c ?d ?e ?f ?g
               (case_arch_capability ?aa ?ab ?ac ?ad)
               ?h ?i ?j ?k
            (capMasterCap cap)"
  by (fastforce simp: ccap_relation_def map_option_Some_eq2
                     Let_def cap_lift_def cap_to_H_def
              split: if_split_asm)

lemma ccap_relation_is_derived_tag_equal:
  "\<lbrakk> is_derived' cs p cap cap'; ccap_relation cap ccap; ccap_relation cap' ccap' \<rbrakk>
  \<Longrightarrow> cap_get_tag ccap' = cap_get_tag ccap"
  unfolding badge_derived'_def is_derived'_def
  by (clarsimp simp: ccap_relation_tag_Master)

lemma ccap_relation_Master_tags_eq:
  "\<lbrakk> capMasterCap cap = capMasterCap cap'; ccap_relation cap ccap; ccap_relation cap' ccap' \<rbrakk>
  \<Longrightarrow> cap_get_tag ccap' = cap_get_tag ccap"
  by (clarsimp simp: ccap_relation_tag_Master)

lemma is_simple_cap_get_tag_relation:
  "ccap_relation cap ccap
     \<Longrightarrow> is_simple_cap_tag (cap_get_tag ccap) = is_simple_cap' cap"
  apply (simp add: is_simple_cap_tag_def is_simple_cap'_def
                   cap_get_tag_isCap)
  apply (auto simp: isCap_simps)
  done

lemma setUntypedCapAsFull_cte_at_wp [wp]:
  "\<lbrace> cte_at' x \<rbrace> setUntypedCapAsFull rvb cap src \<lbrace> \<lambda>_. cte_at' x \<rbrace>"
  apply (clarsimp simp: setUntypedCapAsFull_def)
  apply wp
  done

lemma valid_cap_untyped_inv:
  "valid_cap' (UntypedCap d r n f) s \<Longrightarrow>
    n \<ge> minUntypedSizeBits \<and> is_aligned (of_nat f :: machine_word) minUntypedSizeBits
      \<and> n \<le> maxUntypedSizeBits \<and> n < word_bits"
  apply (clarsimp simp:valid_cap'_def capAligned_def)
  done

lemma update_freeIndex':
  assumes i'_align: "is_aligned (of_nat i' :: machine_word) minUntypedSizeBits"
  assumes sz_bound: "sz \<le> maxUntypedSizeBits"
  assumes i'_bound: "i'\<le> 2^sz"
  shows "ccorres dc xfdc
                 (cte_wp_at' (\<lambda>cte. \<exists>i. cteCap cte = capability.UntypedCap d p sz i) srcSlot)
                 (UNIV \<inter> \<lbrace>\<acute>cap_ptr = cap_Ptr &(cte_Ptr srcSlot\<rightarrow>[''cap_C''])\<rbrace>
                       \<inter> \<lbrace>\<acute>v64 = of_nat i' >> minUntypedSizeBits\<rbrace>) []
                 (updateCap srcSlot (capability.UntypedCap d p sz i'))
                 (Call cap_untyped_cap_ptr_set_capFreeIndex_'proc)"
  proof -
    note i'_bound_concrete
      = order_trans[OF i'_bound power_increasing[OF sz_bound], simplified untypedBits_defs, simplified]
    have i'_bound_word: "(of_nat i' :: machine_word) \<le> 2 ^ maxUntypedSizeBits"
      using order_trans[OF i'_bound power_increasing[OF sz_bound], simplified]
      by (simp add: word_of_nat_le untypedBits_defs)
    show ?thesis
      apply (cinit lift: cap_ptr_' v64_')
       apply (rule ccorres_pre_getCTE)
       apply (rule_tac P="\<lambda>s. ctes_of s srcSlot = Some rv \<and> (\<exists>i. cteCap rv = UntypedCap d p sz i)"
                in ccorres_from_vcg[where P' = UNIV])
       apply (rule allI)
       apply (rule conseqPre)
        apply vcg
       apply (clarsimp simp: guard_simps)
       apply (intro conjI)
        apply (frule (1) rf_sr_ctes_of_clift)
        apply (clarsimp simp: typ_heap_simps)
       apply (frule (1) rf_sr_ctes_of_clift)
       apply (clarsimp simp: split_def)
       apply (simp add: hrs_htd_def typ_heap_simps)
       apply (rule fst_setCTE[OF ctes_of_cte_at], assumption)
       apply (erule bexI[rotated], clarsimp)
       apply (frule (1) rf_sr_ctes_of_clift)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                             cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
       apply (simp add: cpspace_relation_def)
       apply (clarsimp simp: typ_heap_simps')
       apply (rule conjI)
        apply (erule (2) cpspace_cte_relation_upd_capI)
        apply (simp only: cte_lift_def split: option.splits; simp)
        apply (simp add: cap_to_H_def Let_def split: cap_CL.splits if_split_asm)
        apply (case_tac y)
        apply (simp add: cap_lift_def Let_def split: if_split_asm)
        apply (case_tac cte', simp)
        apply (clarsimp simp: ccap_relation_def cap_lift_def cap_get_tag_def cap_to_H_def)
        apply (thin_tac _)+
        apply (simp add: mask_def to_bool_and_1 nth_shiftr word_ao_dist word_bool_alg.conj.assoc)
        apply (rule inj_onD[OF word_unat.Abs_inj_on[where 'a=machine_word_len]], simp)
          apply (cut_tac i'_align i'_bound_word)
          apply (simp add: is_aligned_mask)
          apply word_bitwise
          subgoal by (simp add: word_size untypedBits_defs)
         apply (cut_tac i'_bound_concrete)
         subgoal by (simp add: unats_def)
        subgoal by (simp add: word_unat.Rep[where 'a=machine_word_len, simplified])
       apply (erule_tac t = s' in ssubst)
       apply clarsimp
       apply (rule conjI)
        subgoal by (erule (1) setCTE_tcb_case)
       apply (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
                             packed_heap_update_collapse_hrs)
      by (clarsimp simp: cte_wp_at_ctes_of)
  qed

lemma update_freeIndex:
  "ccorres dc xfdc
           (valid_objs' and cte_wp_at' (\<lambda>cte. \<exists>i. cteCap cte = UntypedCap d p sz i) srcSlot
                 and (\<lambda>_. is_aligned (of_nat i' :: machine_word) minUntypedSizeBits \<and> i' \<le> 2 ^ sz))
           (UNIV \<inter> \<lbrace>\<acute>cap_ptr = cap_Ptr &(cte_Ptr srcSlot\<rightarrow>[''cap_C''])\<rbrace>
                 \<inter> \<lbrace>\<acute>v64 = of_nat i' >> minUntypedSizeBits\<rbrace>) []
           (updateCap srcSlot (UntypedCap d p sz i'))
           (Call cap_untyped_cap_ptr_set_capFreeIndex_'proc)"
  apply (rule ccorres_assume_pre, rule ccorres_guard_imp)
    apply (rule update_freeIndex'; clarsimp simp: cte_wp_at_ctes_of)
    apply (case_tac cte; clarsimp dest!: ctes_of_valid_cap' simp: valid_cap'_def)
   by auto

(* FIXME: move *)
lemma ccorres_cases:
  assumes P:    " P \<Longrightarrow> ccorres r xf G G' hs a b"
  assumes notP: "\<not>P \<Longrightarrow> ccorres r xf H H' hs a b"
  shows "ccorres r xf (\<lambda>s. (P \<longrightarrow> G s) \<and> (\<not>P \<longrightarrow> H s))
                      ({s. P \<longrightarrow> s \<in> G'} \<inter> {s. \<not>P \<longrightarrow> s \<in> H'})
                      hs a b"
  apply (cases P, auto simp: P notP)
  done

lemma capBlockSize_CL_maxSize:
  " \<lbrakk> cap_get_tag c = scast cap_untyped_cap \<rbrakk> \<Longrightarrow> capBlockSize_CL (cap_untyped_cap_lift c) < 0x40"
  apply (clarsimp simp: cap_untyped_cap_lift_def)
  apply (clarsimp simp: cap_lift_def)
  apply (clarsimp simp: cap_untyped_cap_def cap_null_cap_def)
  apply (rule word_and_less')
  apply (simp add: mask_def)
  done

lemma setUntypedCapAsFull_ccorres [corres]:
  notes if_split [split del]
  notes Collect_const [simp del]
  notes Collect_True [simp] Collect_False [simp]
  shows
  "ccorres dc xfdc
      ((cte_wp_at' (\<lambda>c. (cteCap c) = srcCap) srcSlot) and valid_mdb' and pspace_aligned' and valid_objs'
          and (K (isUntypedCap newCap \<longrightarrow> (minUntypedSizeBits \<le> capBlockSize newCap)))
          and (K (isUntypedCap srcCap \<longrightarrow> (minUntypedSizeBits \<le> capBlockSize srcCap))))
      (UNIV \<inter> {s. ccap_relation srcCap (srcCap_' s)}
            \<inter> {s. ccap_relation newCap (newCap_' s)}
            \<inter> {s. srcSlot_' s = Ptr srcSlot})
      []
      (setUntypedCapAsFull srcCap newCap srcSlot)
      (Call setUntypedCapAsFull_'proc)"
  apply (cinit lift: srcCap_' newCap_' srcSlot_')
   apply (rule ccorres_if_lhs)
    apply (clarsimp simp: isCap_simps)
    apply csymbr
    apply csymbr
    apply (simp add: if_then_0_else_1 if_then_1_else_0 cap_get_tag_isCap_unfolded_H_cap)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: cap_get_tag_isCap_unfolded_H_cap ccorres_cond_univ_iff)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply (frule cap_get_tag_to_H(9))
     apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
    apply (rotate_tac 1)
    apply (frule cap_get_tag_to_H(9))
     apply (simp add: cap_get_tag_isCap_unfolded_H_cap)
    apply simp
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply csymbr
    apply (simp add: ccorres_cond_univ_iff)
    apply csymbr+
    apply (rule ccorres_move_c_guard_cte)
    apply (rule ccorres_Guard)
    apply (rule ccorres_call)
       apply (rule update_freeIndex [unfolded dc_def])
      apply simp
     apply simp
    apply simp
   apply clarsimp
   apply (csymbr)
   apply (csymbr)
   apply (simp add: cap_get_tag_isCap)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (rule ccorres_rhs_assoc)+
    apply csymbr
    apply csymbr
    apply (simp add: cap_get_tag_isCap)
    apply (rule ccorres_Cond_rhs)
     apply (rule ccorres_rhs_assoc)+
     apply csymbr
     apply csymbr
     apply csymbr
     apply (rule ccorres_cases [where P="capPtr srcCap = capPtr newCap"])
      apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply csymbr
      apply (clarsimp simp: cap_get_tag_to_H cap_get_tag_UntypedCap split: if_split_asm)
      apply (rule ccorres_cond_false)
      apply (rule ccorres_return_Skip [unfolded dc_def])
     apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
     apply (rule ccorres_cond_false)
     apply (rule ccorres_return_Skip [unfolded dc_def])
    apply (rule ccorres_return_Skip [unfolded dc_def])
   apply clarsimp
   apply (rule ccorres_cond_false)
   apply (rule ccorres_return_Skip [unfolded dc_def])
  apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap')
  apply (clarsimp simp: untypedBits_defs)
  apply (intro conjI impI allI)
        apply (erule cte_wp_at_weakenE')
        apply (clarsimp simp: cap_get_tag_isCap[symmetric] cap_get_tag_UntypedCap split: if_split_asm)
       apply clarsimp
       apply (drule valid_cap_untyped_inv,clarsimp simp:max_free_index_def)
       apply (rule is_aligned_weaken)
        apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
       apply assumption
      apply (clarsimp simp: max_free_index_def shiftL_nat valid_cap'_def capAligned_def)
     apply (simp add:power_minus_is_div unat_sub word_le_nat_alt t2p_shiftr)
     apply clarsimp
     apply (erule cte_wp_at_weakenE', simp)
    apply clarsimp
    apply (drule valid_cap_untyped_inv)
    apply (clarsimp simp: max_free_index_def t2p_shiftr unat_sub word_le_nat_alt word_bits_def)
   apply (rule word_less_imp_diff_less)
    apply (subst (asm) eq_commute, fastforce simp: unat_sub word_le_nat_alt)
   apply (rule capBlockSize_CL_maxSize)
   apply (clarsimp simp: cap_get_tag_UntypedCap)
  apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap)
  done

lemma ccte_lift:
  "\<lbrakk>(s, s') \<in> rf_sr; cslift s' (cte_Ptr p) = Some cte';
    cte_lift cte' = Some y; c_valid_cte cte'\<rbrakk>
   \<Longrightarrow> ctes_of s p = Some (cte_to_H (the (cte_lift cte')))"
  apply (clarsimp simp:rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
  apply (drule(1) cmap_relation_cs_atD)
   apply simp
  apply (clarsimp simp:ccte_relation_def)
  done

lemma cmdb_node_relation_mdbNext:
  "cmdbnode_relation n n'
         \<Longrightarrow> mdbNext_CL (mdb_node_lift n') = mdbNext n"
 by (simp add:cmdbnode_relation_def)

lemma cslift_ptr_safe:
  "cslift x ptr = Some a
  \<Longrightarrow> ptr_safe ptr (hrs_htd (t_hrs_' (globals x)))"
  apply (rule_tac h = "fst (t_hrs_' (globals x))"
        in lift_t_ptr_safe[where g = c_guard])
  apply (fastforce simp add:typ_heap_simps hrs_htd_def)
  done

lemma ccorres_move_ptr_safe:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C' hs a c \<Longrightarrow>
  ccorres_underlying rf_sr \<Gamma> r xf arrel axf
  (A and K (dest = cte_Ptr (ptr_val dest)) and cte_wp_at' (\<lambda>_. True) (ptr_val dest))
  (C' \<inter> \<lbrace>True\<rbrace>) hs a (Guard MemorySafety \<lbrace>ptr_safe (dest) (hrs_htd \<acute>t_hrs) \<rbrace> c)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Guard)
   apply simp
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) rf_sr_ctes_of_clift)
  apply (case_tac dest)
  apply (clarsimp simp:ptr_coerce_def)
  apply (erule cslift_ptr_safe)
  done

lemma ccorres_move_ptr_safe_Seq:
  "ccorres_underlying rf_sr \<Gamma> r xf arrel axf A C' hs a (c;;d) \<Longrightarrow>
  ccorres_underlying rf_sr \<Gamma> r xf arrel axf
  (A and cte_wp_at' (\<lambda>_. True) (ptr_val dest) and K (dest = cte_Ptr (ptr_val dest)))
  (C' \<inter> \<lbrace>True\<rbrace>) hs a
  (Guard MemorySafety \<lbrace>ptr_safe (dest) (hrs_htd \<acute>t_hrs) \<rbrace> c;;d)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Guard_Seq)
   apply simp
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (drule(1) rf_sr_ctes_of_clift)
  apply clarsimp
  apply (erule cslift_ptr_safe)
  done

lemmas ccorres_move_guard_ptr_safe = ccorres_move_ptr_safe_Seq ccorres_move_ptr_safe

lemma cteInsert_ccorres:
  "ccorres dc xfdc
           (cte_wp_at' (\<lambda>scte. capMasterCap (cteCap scte) = capMasterCap cap \<or> is_simple_cap' cap) src
               and valid_mdb' and valid_objs' and pspace_aligned' and pspace_canonical'
               and (valid_cap' cap))
           (UNIV \<inter> {s. destSlot_' s = Ptr dest}
                 \<inter> {s. srcSlot_' s = Ptr src}
                 \<inter> {s. ccap_relation cap (newCap_' s)}) []
           (cteInsert cap src dest)
           (Call cteInsert_'proc)"
  supply ctes_of_aligned_bits[simp]
  apply (cinit (no_ignore_call) lift: destSlot_' srcSlot_' newCap_'
    simp del: return_bind simp add: Collect_const)
   apply (rule ccorres_move_c_guard_cte)
   apply (ctac pre: ccorres_pre_getCTE)
     apply (rule ccorres_move_c_guard_cte)
     apply (ctac pre: ccorres_pre_getCTE)
       apply (ctac (no_vcg) add: revokable_ccorres)
        apply (ctac (c_lines 3) add: cteInsert_ccorres_mdb_helper)
          apply (simp del: Collect_const)
          apply (rule ccorres_pre_getCTE ccorres_assert)+
          apply (ctac add: setUntypedCapAsFull_ccorres)
            apply (rule ccorres_move_c_guard_cte)
            apply (ctac)
              apply (rule ccorres_move_c_guard_cte)
              apply ctac
                apply (rule ccorres_move_c_guard_cte)
                apply (ctac(no_vcg))
                 apply csymbr
                 apply (erule_tac t = ret__unsigned_longlong in ssubst)
                 apply (rule ccorres_cond_both [where R = \<top>, simplified])
                   apply (erule mdbNext_not_zero_eq)
                  apply csymbr
                  apply simp
                  apply (rule ccorres_move_c_guard_cte)
                  apply (simp add:dc_def[symmetric])
                  apply (ctac ccorres:ccorres_updateMDB_set_mdbPrev)
                 apply (simp add:dc_def[symmetric])
                 apply (ctac ccorres: ccorres_updateMDB_skip)
                apply (wp static_imp_wp)+
              apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
              apply vcg
             apply (wp static_imp_wp)
            apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
            apply vcg
           apply (clarsimp simp:cmdb_node_relation_mdbNext)
           apply (wp setUntypedCapAsFull_cte_at_wp static_imp_wp)
          apply (clarsimp simp: Collect_const_mem dc_def split del: if_split)
          apply (vcg exspec=setUntypedCapAsFull_modifies)
         apply wp
        apply vcg
       apply wp
      apply wp
     apply vcg
    apply wp
   apply vcg
  apply (simp add: Collect_const_mem split del: if_split) \<comment> \<open>Takes a while\<close>
  apply (rule conjI)
   apply (clarsimp simp: conj_comms cte_wp_at_ctes_of)
   apply (intro conjI)
      apply clarsimp
     apply simp
    apply simp
   apply (clarsimp simp: ctes_of_canonical objBits_defs cte_level_bits_def)
   apply (rule conjI)
    apply (clarsimp simp: isUntypedCap_def split: capability.split_asm)
    apply (frule valid_cap_untyped_inv)
    apply clarsimp
   apply (rule conjI)
    apply (case_tac ctea)
    apply (clarsimp simp: isUntypedCap_def split: capability.splits)
    apply (frule valid_cap_untyped_inv[OF ctes_of_valid_cap'])
     apply fastforce
    apply clarsimp+
   apply (drule valid_dlist_nextD)
     apply (simp add:valid_mdb'_def valid_mdb_ctes_def)
    apply simp
   apply clarsimp
  apply (clarsimp simp: map_comp_Some_iff cte_wp_at_ctes_of
             split del: if_split)
  apply (clarsimp simp: typ_heap_simps c_guard_clift split_def)
  apply (clarsimp simp: is_simple_cap_get_tag_relation ccte_relation_ccap_relation cmdb_node_relation_mdbNext[symmetric])
  done

(****************************************************************************)
(*                                                                          *)
(* Lemmas dealing with updateMDB on Haskell side and IF-THEN-ELSE on C side *)
(*                                                                          *)
(****************************************************************************)

lemma updateMDB_mdbNext_set_mdbPrev:
 "\<lbrakk> slotc = Ptr slota; cmdbnode_relation mdba mdbc\<rbrakk> \<Longrightarrow>
  ccorres dc xfdc
          (\<lambda>s. is_aligned slota cteSizeBits)
          UNIV hs
          (updateMDB (mdbNext mdba) (mdbPrev_update (\<lambda>_. slota)))
          (IF mdbNext_CL (mdb_node_lift mdbc) \<noteq> 0
           THEN Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (mdbNext_CL (mdb_node_lift mdbc)) :: cte_C ptr)\<rbrace>
                      (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr (mdbNext_CL (mdb_node_lift mdbc)):: cte_C ptr
                                                                 \<rightarrow>[''cteMDBNode_C'']),
                                        v64_' := ptr_val slotc |))
                            mdb_node_ptr_set_mdbPrev_'proc
                            (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
           FI)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_cond_both[where R=\<top>, simplified])
     apply (erule mdbNext_not_zero_eq)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbPrev)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply (clarsimp simp: cmdbnode_relation_def cte_wp_at_ctes_of)
  done

lemma updateMDB_mdbPrev_set_mdbNext:
 "\<lbrakk> slotc = Ptr slota; cmdbnode_relation mdba mdbc\<rbrakk> \<Longrightarrow>
  ccorres dc xfdc
          (\<lambda>s. is_aligned slota cteSizeBits \<and> canonical_address slota)
          UNIV hs
          (updateMDB (mdbPrev mdba) (mdbNext_update (\<lambda>_. slota)))
          (IF mdbPrev_CL (mdb_node_lift mdbc) \<noteq> 0
           THEN Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr (mdbPrev_CL (mdb_node_lift mdbc)):: cte_C ptr)\<rbrace>
                      (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr (mdbPrev_CL (mdb_node_lift mdbc)):: cte_C ptr
                                                                  \<rightarrow>[''cteMDBNode_C'']),
                                        v64_' := ptr_val slotc |))
                            mdb_node_ptr_set_mdbNext_'proc
                            (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
           FI)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_cond_both[where R=\<top>, simplified])
     apply (erule mdbPrev_not_zero_eq)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbNext)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply (clarsimp simp: cte_wp_at_ctes_of cmdbnode_relation_def)
  done


(************************************************************************)
(*                                                                      *)
(* cteMove_ccorres ******************************************************)
(*                                                                      *)
(************************************************************************)

(* FIXME: rename *)
lemma is_aligned_3_prev:
  "\<lbrakk> valid_mdb' s; pspace_aligned' s; ctes_of s p = Some cte \<rbrakk>
  \<Longrightarrow> is_aligned (mdbPrev (cteMDBNode cte)) cteSizeBits"
  apply (cases "mdbPrev (cteMDBNode cte) = 0", simp)
  apply (drule (2) valid_mdb_ctes_of_prev)
  apply (clarsimp simp: cte_wp_at_ctes_of cteSizeBits_eq ctes_of_aligned_bits)
  done

(* FIXME: rename *)
lemma is_aligned_3_next:
  "\<lbrakk> valid_mdb' s; pspace_aligned' s; ctes_of s p = Some cte \<rbrakk>
  \<Longrightarrow> is_aligned (mdbNext (cteMDBNode cte)) cteSizeBits"
  apply (cases "mdbNext (cteMDBNode cte) = 0", simp)
  apply (drule (2) valid_mdb_ctes_of_next)
  apply (clarsimp simp: cte_wp_at_ctes_of cteSizeBits_eq ctes_of_aligned_bits)
  done

lemma cteMove_ccorres:
  "ccorres dc xfdc
       (valid_mdb' and pspace_aligned' and pspace_canonical')
       (UNIV \<inter> {s. destSlot_' s = Ptr dest}
             \<inter> {s. srcSlot_' s = Ptr src}
             \<inter> {s. ccap_relation cap (newCap_' s)}) []
       (cteMove cap src dest)
       (Call cteMove_'proc)"
  apply (cinit (no_ignore_call) lift: destSlot_' srcSlot_' newCap_' simp del: return_bind)
   apply (ctac pre: ccorres_pre_getCTE ccorres_assert)
     apply (ctac+, csymbr+)+
             apply (erule_tac t=ret__unsigned_longlong in ssubst)
             apply (ctac add: updateMDB_mdbPrev_set_mdbNext)
               apply csymbr
               apply csymbr
               apply (erule_tac t=ret__unsigned_longlong in ssubst)
               apply (rule updateMDB_mdbNext_set_mdbPrev)
                apply simp+
              apply (wp, vcg)+
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of cteSizeBits_eq ctes_of_canonical ctes_of_aligned_bits)
   apply assumption
  apply (clarsimp simp: ccap_relation_NullCap_iff cmdbnode_relation_def
                        mdb_node_to_H_def nullMDBNode_def false_def)
  done

(************************************************************************)
(*                                                                      *)
(* lemmas used in cteSwap_ccorres ***************************************)
(*                                                                      *)
(************************************************************************)



(*---------------------------------------------------------------------------------------*)
(* corres lemma for return of mdbnode but 'safer' than ccorres_return_cte_mdbnode ------ *)
(*---------------------------------------------------------------------------------------*)

lemma ccorres_return_cte_mdbnode_safer:
  fixes ptr' :: "cstate \<Rightarrow> cte_C ptr"
  assumes r1: "\<And>s s' g. (s, s') \<in> rf_sr \<Longrightarrow> (s, xfu g s') \<in> rf_sr"
  and xf_xfu: "\<And>s g. xf (xfu g s) = g s"
  shows "ccorres cmdbnode_relation xf
         (\<lambda>s. \<exists> cte'. ctes_of s ptr = Some cte' \<and> cteMDBNode cte = cteMDBNode cte') {s. ptr_val (ptr' s) = ptr}  hs
         (return (cteMDBNode cte))
         (Basic (\<lambda>s. xfu (\<lambda>_. h_val  (hrs_mem (t_hrs_' (globals s)))
           (Ptr &(ptr' s \<rightarrow>[''cteMDBNode_C'']))) s))"
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp add: return_def)
  apply rule
  apply (erule r1)
  apply (simp add: xf_xfu)
  apply (drule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  done






(*-----------------------------------------------------------------------*)
(* lemmas about map and hrs_mem -----------------------------------------*)
(*-----------------------------------------------------------------------*)

declare modify_map_exists_cte[simp]







(*------------------------------------------------------------------------------*)
(* lemmas about pointer equality given valid_mdb (prev\<noteq>next, prev\<noteq>myself, etc) *)
(*------------------------------------------------------------------------------*)

lemma valid_mdb_Prev_neq_Next:
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte; mdbPrev (cteMDBNode cte) \<noteq> 0  \<rbrakk> \<Longrightarrow>
     (mdbNext (cteMDBNode cte)) \<noteq> (mdbPrev (cteMDBNode cte))"
  apply (simp add: valid_mdb'_def)
  apply (simp add: valid_mdb_ctes_def)
  apply (elim conjE)
  apply (drule (1) mdb_chain_0_no_loops)
  apply (simp add: valid_dlist_def)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=cte in allE)
  apply (simp add: Let_def)
  apply clarsimp
  apply (drule_tac s="mdbNext (cteMDBNode cte)" in sym)
  apply simp
  apply (simp add: no_loops_def)
  apply (erule_tac x= "(mdbNext (cteMDBNode cte))" in allE)
  apply (erule notE, rule trancl_trans)
    apply (rule r_into_trancl)
    apply (simp add: mdb_next_unfold)
  apply (rule r_into_trancl)
  apply (simp add: mdb_next_unfold)
done

lemma valid_mdb_Prev_neq_itself:
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte  \<rbrakk> \<Longrightarrow>
     (mdbPrev (cteMDBNode cte)) \<noteq>  p"
  apply (unfold valid_mdb'_def)
  apply (simp add: CSpace_I.no_self_loop_prev)
done

lemma valid_mdb_Next_neq_itself:
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte  \<rbrakk> \<Longrightarrow>
     (mdbNext (cteMDBNode cte)) \<noteq>  p"
  apply (unfold valid_mdb'_def)
  apply (simp add: CSpace_I.no_self_loop_next)
done

lemma valid_mdb_not_same_Next :
    "\<lbrakk> valid_mdb' s; p\<noteq>p'; ctes_of s p = Some cte; ctes_of s p' = Some cte';
       (mdbNext (cteMDBNode cte))\<noteq>0 \<or> (mdbNext (cteMDBNode cte'))\<noteq>0 \<rbrakk> \<Longrightarrow>
     (mdbNext (cteMDBNode cte)) \<noteq>  (mdbNext (cteMDBNode cte'))  "
  apply (clarsimp)
  apply (case_tac cte, clarsimp)
  apply (rename_tac capability mdbnode)
  apply (case_tac cte', clarsimp)
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   apply (drule (2) mdb_ptr.p_nextD)
   apply clarsimp
  apply (unfold mdb_ptr_def vmdb_def mdb_ptr_axioms_def valid_mdb'_def, simp)
  done

lemma valid_mdb_not_same_Prev :
    "\<lbrakk> valid_mdb' s; p\<noteq>p'; ctes_of s p = Some cte; ctes_of s p' = Some cte';
       (mdbPrev (cteMDBNode cte))\<noteq>0 \<or> (mdbPrev (cteMDBNode cte'))\<noteq>0 \<rbrakk> \<Longrightarrow>
     (mdbPrev (cteMDBNode cte)) \<noteq>  (mdbPrev (cteMDBNode cte'))  "
  apply (clarsimp)
  apply (case_tac cte, clarsimp)
  apply (rename_tac capability mdbnode)
  apply (case_tac cte', clarsimp)
  apply (subgoal_tac "mdb_ptr (ctes_of s) p capability mdbnode")
   apply (drule (2) mdb_ptr.p_prevD)
   apply clarsimp
  apply (unfold mdb_ptr_def vmdb_def mdb_ptr_axioms_def valid_mdb'_def, simp)
  done




(*---------------------------------------------------------------------------------*)
(* lemmas to simplify the big last goal on C side to avoid proving things twice ---*)
(*---------------------------------------------------------------------------------*)

lemma c_guard_and_h_t_valid_eq_h_t_valid:
     "(POINTER \<noteq> 0 \<longrightarrow>
         c_guard ((Ptr &(Ptr POINTER ::cte_C ptr \<rightarrow>[''cteMDBNode_C''])) ::mdb_node_C ptr)  \<and>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr)) =
      (POINTER \<noteq> 0 \<longrightarrow>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr))"
  apply (rule iffI, clarsimp+)
  apply (rule c_guard_field_lvalue)
  apply (rule c_guard_h_t_valid, assumption)
  apply (fastforce simp: typ_uinfo_t_def)+
done


lemma c_guard_and_h_t_valid_and_rest_eq_h_t_valid_and_rest:
     "(POINTER \<noteq> 0 \<longrightarrow>
         c_guard ((Ptr &(Ptr POINTER ::cte_C ptr \<rightarrow>[''cteMDBNode_C''])) ::mdb_node_C ptr)  \<and>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr) \<and> REST) =
      (POINTER \<noteq> 0 \<longrightarrow>
         s' \<Turnstile>\<^sub>c (Ptr (POINTER)::cte_C ptr) \<and> REST)"
  apply (rule iffI, clarsimp+)
  apply (rule c_guard_field_lvalue)
  apply (rule c_guard_h_t_valid, assumption)
  apply (fastforce simp: typ_uinfo_t_def)+
done


(************************************************************************)
(*                                                                      *)
(* cteSwap_ccorres ******************************************************)
(*                                                                      *)
(************************************************************************)

lemma cteSwap_ccorres:
  "ccorres dc xfdc
           (valid_mdb' and pspace_aligned' and pspace_canonical'
                       and (\<lambda>_. slot1 \<noteq> slot2))
           (UNIV \<inter> {s. slot1_' s = Ptr slot1}
                 \<inter> {s. slot2_' s = Ptr slot2}
                 \<inter> {s. ccap_relation cap1 (cap1_' s)}
                 \<inter> {s. ccap_relation cap2 (cap2_' s)})
           []
           (cteSwap cap1 slot1 cap2 slot2)
           (Call cteSwap_'proc)"
  supply ctes_of_aligned_bits[simp]
  apply (cinit (no_ignore_call) lift: slot1_' slot2_' cap1_' cap2_' simp del: return_bind)
   apply (ctac (no_vcg) pre: ccorres_pre_getCTE ccorres_move_guard_ptr_safe)
     apply (rule ccorres_updateCap_cte_at)
     apply (ctac (no_vcg) add: ccorres_return_cte_mdbnode_safer [where ptr=slot1])+
         apply csymbr
         apply csymbr
         apply (erule_tac t=ret__unsigned_longlong in ssubst)
         apply (ctac (no_vcg) add: updateMDB_mdbPrev_set_mdbNext)
           apply csymbr
           apply csymbr
           apply (erule_tac t=ret__unsigned_longlong in ssubst)
           apply (ctac (no_vcg) add: updateMDB_mdbNext_set_mdbPrev)
             apply (rule ccorres_move_c_guard_cte)
             apply (ctac (no_vcg) pre: ccorres_getCTE ccorres_move_guard_ptr_safe
                                  add: ccorres_return_cte_mdbnode[where ptr=slot2]
                                       ccorres_move_guard_ptr_safe)+
                   apply csymbr
                   apply csymbr
                   apply (erule_tac t=ret__unsigned_longlong in ssubst)
                   apply (ctac (no_vcg) add: updateMDB_mdbPrev_set_mdbNext)
                     apply csymbr
                     apply csymbr
                     apply (erule_tac t=ret__unsigned_longlong in ssubst)
                     apply (ctac (no_vcg) add: updateMDB_mdbNext_set_mdbPrev)
                    apply wp
                   apply simp
                  apply wp
                 apply simp
                apply wp
               apply simp
              apply wp
             apply simp
            apply (clarsimp simp : cte_wp_at_ctes_of)
            apply wp
           apply simp
          apply wp
         apply simp
        apply wp
       apply simp
      apply (clarsimp simp : cte_wp_at_ctes_of)
      apply (wp updateCap_ctes_of_wp)
     apply simp
    apply (clarsimp simp : cte_wp_at_ctes_of)
    apply (wp updateCap_ctes_of_wp)
   apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (apply_conjunct \<open>match conclusion in \<open>no_0 _\<close>
          \<Rightarrow> \<open>simp add: valid_mdb'_def, erule (1) valid_mdb_ctesE\<close>\<close>)
  apply (case_tac cte; simp add: modify_map_if ctes_of_canonical)
  done

(* todo change in cteMove (\<lambda>s. ctes_of s src = Some scte) *)


(************************************************************************)
(*                                                                      *)
(* lemmas used in emptySlot_ccorres *************************************)
(*                                                                      *)
(************************************************************************)


declare if_split [split del]

(* rq CALL mdb_node_ptr_set_mdbNext_'proc \<dots>) is a printing bug
   one should write  CALL mdb_node_ptr_set_mdbNext
*)

lemma not_NullCap_eq_not_cap_null_cap:
  " \<lbrakk>ccap_relation cap cap' ; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow>
   (cap \<noteq> NullCap) = (s' \<in> {_. (cap_get_tag cap' \<noteq> scast cap_null_cap)})"
  apply (rule iffI)
   apply (case_tac "cap_get_tag cap' \<noteq> scast cap_null_cap", clarsimp+)
   apply (erule notE)
   apply (simp add: cap_get_tag_NullCap)
  apply (case_tac "cap_get_tag cap' \<noteq> scast cap_null_cap")
   apply (rule notI)
   apply (erule notE)
   apply (simp add: cap_get_tag_NullCap)
  apply clarsimp
done

lemma emptySlot_helper:
  fixes mdbNode
  defines "nextmdb \<equiv> Ptr &(Ptr ((mdbNext_CL (mdb_node_lift mdbNode)))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr"
  defines "nextcte \<equiv> Ptr ((mdbNext_CL (mdb_node_lift mdbNode)))::cte_C ptr"
  shows "\<lbrakk>cmdbnode_relation rva mdbNode\<rbrakk>
    \<Longrightarrow> ccorres dc xfdc \<top> UNIV hs
           (updateMDB (mdbNext rva)
             (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged rva) (mdbPrev_update (\<lambda>_. mdbPrev rva) mdb)))
           (IF mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0 THEN
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (CALL mdb_node_ptr_set_mdbPrev(nextmdb, ptr_val (Ptr (mdbPrev_CL (mdb_node_lift mdbNode)))))
            FI;;
            IF mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0 THEN
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (\<acute>ret__unsigned_longlong :== CALL mdb_node_get_mdbFirstBadged(h_val (hrs_mem \<acute>t_hrs) nextmdb));;
              \<acute>ret__int :== (if \<acute>ret__unsigned_longlong \<noteq> 0 then 1 else 0);;
              IF \<acute>ret__int \<noteq> 0 THEN
                SKIP
              ELSE
                \<acute>ret__unsigned_longlong :== CALL mdb_node_get_mdbFirstBadged(mdbNode);;
                \<acute>ret__int :== (if \<acute>ret__unsigned_longlong \<noteq> 0 then 1 else 0)
              FI;;
              Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t  nextcte\<rbrace>
               (CALL mdb_node_ptr_set_mdbFirstBadged(nextmdb,scast \<acute>ret__int))
            FI)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_updateMDB_cte_at)
  apply (subgoal_tac "mdbNext rva=(mdbNext_CL (mdb_node_lift mdbNode))")
   prefer 2
   apply (simp add: cmdbnode_relation_def)

  apply (case_tac "mdbNext rva \<noteq> 0")
   apply (case_tac "mdbNext_CL (mdb_node_lift mdbNode) = 0", simp)

   \<comment> \<open>case where mdbNext rva \<noteq> 0 and mdbNext_CL (mdb_node_lift mdbNode) \<noteq> 0\<close>
   apply (unfold updateMDB_def)
   apply (clarsimp simp: Let_def)
   apply (rule ccorres_pre_getCTE [where P = "\<lambda>cte s. ctes_of s (mdbNext rva) = Some cte" and P' = "\<lambda>_. UNIV"])
   apply (rule ccorres_from_vcg)
   apply (rule allI)
   apply (rule conseqPre, vcg)
   apply clarsimp

   apply (frule(1) rf_sr_ctes_of_clift)
   apply (clarsimp simp: typ_heap_simps' nextmdb_def if_1_0_0 nextcte_def)
   apply (intro conjI impI allI)
     \<comment> \<open>\<dots> \<exists>x\<in>fst \<dots>\<close>
     apply clarsimp
     apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
     apply (erule bexI [rotated])
     apply (frule (1) rf_sr_ctes_of_clift)
     apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
                Let_def cpspace_relation_def)
     apply (rule conjI)
      prefer 2
      apply (erule_tac t = s' in ssubst)
      apply (simp add: carch_state_relation_def cmachine_state_relation_def
                       cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                       h_t_valid_clift_Some_iff typ_heap_simps'
                 cong: lifth_update)
      apply (erule (1) setCTE_tcb_case)

     apply (erule (2)  cspace_cte_relation_upd_mdbI)
     apply (simp add: cmdbnode_relation_def)
     apply (simp add: mdb_node_to_H_def)

     apply (subgoal_tac "mdbFirstBadged_CL (mdb_node_lift mdbNode) && mask (Suc 0) =
                         mdbFirstBadged_CL (mdb_node_lift mdbNode)")
      prefer 2
      subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
     apply (subgoal_tac "mdbFirstBadged_CL (cteMDBNode_CL y) && mask (Suc 0) =
                         mdbFirstBadged_CL (cteMDBNode_CL y)")
      prefer 2
      apply (drule cteMDBNode_CL_lift [symmetric])
      subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
     subgoal by (simp add: to_bool_def mask_def)
   \<comment> \<open>\<dots> \<exists>x\<in>fst \<dots>\<close>
   apply clarsimp
   apply (rule fst_setCTE [OF ctes_of_cte_at], assumption )
   apply (erule bexI [rotated])
   apply (frule (1) rf_sr_ctes_of_clift)
   apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps
              Let_def cpspace_relation_def)
   apply (rule conjI)
    prefer 2
    apply (erule_tac t = s' in ssubst)
    apply (simp add: carch_state_relation_def cmachine_state_relation_def
                     cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"]
                     typ_heap_simps' h_t_valid_clift_Some_iff
               cong: lifth_update)
    apply (erule (1) setCTE_tcb_case)

   apply (erule (2)  cspace_cte_relation_upd_mdbI)
   apply (simp add: cmdbnode_relation_def)
   apply (simp add: mdb_node_to_H_def)

   apply (subgoal_tac "mdbFirstBadged_CL (mdb_node_lift mdbNode) && mask (Suc 0) =
                       mdbFirstBadged_CL (mdb_node_lift mdbNode)")
    prefer 2
    subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
   apply (subgoal_tac "mdbFirstBadged_CL (cteMDBNode_CL y) && mask (Suc 0) =
                       mdbFirstBadged_CL (cteMDBNode_CL y)")
    prefer 2
    apply (drule cteMDBNode_CL_lift [symmetric])
    subgoal by (simp add: mdb_node_lift_def mask_def word_bw_assocs)
   apply (simp add: to_bool_def mask_def split: if_split)

  \<comment> \<open>trivial case where mdbNext rva = 0\<close>
   apply (simp add:ccorres_cond_empty_iff)
   apply (rule ccorres_guard_imp2)
   apply (rule ccorres_return_Skip)
   apply simp
  apply (clarsimp simp: cmdbnode_relation_def)
done



(************************************************************************)
(*                                                                      *)
(* emptySlot_ccorres ****************************************************)
(*                                                                      *)
(************************************************************************)


(* ML "set CtacImpl.trace_ctac"*)


lemma mdbNext_CL_mdb_node_lift_eq_mdbNext:
  "cmdbnode_relation n n' \<Longrightarrow>  (mdbNext_CL (mdb_node_lift n')) =(mdbNext n)"
  by (erule cmdbnode_relationE, fastforce simp: mdbNext_to_H)

lemma mdbPrev_CL_mdb_node_lift_eq_mdbPrev:
  "cmdbnode_relation n n' \<Longrightarrow>  (mdbPrev_CL (mdb_node_lift n')) =(mdbPrev n)"
  by (erule cmdbnode_relationE, fastforce simp: mdbNext_to_H)


lemma mdbNext_not_zero_eq_simpler:
  "cmdbnode_relation n n' \<Longrightarrow> (mdbNext n \<noteq> 0) = (mdbNext_CL (mdb_node_lift n') \<noteq> 0)"
  apply clarsimp
  apply (erule cmdbnode_relationE)
  apply (fastforce simp: mdbNext_to_H)
  done



lemma mdbPrev_not_zero_eq_simpler:
  "cmdbnode_relation n n' \<Longrightarrow> (mdbPrev n \<noteq> 0) = (mdbPrev_CL (mdb_node_lift n') \<noteq> 0)"
  apply clarsimp
  apply (erule cmdbnode_relationE)
  apply (fastforce simp: mdbPrev_to_H)
  done

lemma h_t_valid_and_cslift_and_c_guard_field_mdbPrev_CL:
      " \<lbrakk>(s, s') \<in> rf_sr; cte_at' slot s;  valid_mdb' s; cslift s' (Ptr slot) = Some cte'\<rbrakk>
       \<Longrightarrow> (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte')) \<noteq> 0) \<longrightarrow>
           s' \<Turnstile>\<^sub>c ( Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) \<and>
           (\<exists> cten. cslift s' (Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) = Some cten)  \<and>
           c_guard (Ptr &(Ptr (mdbPrev_CL (mdb_node_lift (cteMDBNode_C cte')))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr)"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) valid_mdb_ctes_of_prev)
  apply (frule (2) rf_sr_cte_relation)
  apply (drule ccte_relation_cmdbnode_relation)
  apply (simp add: mdbPrev_not_zero_eq_simpler)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift [rotated])+
  apply (clarsimp simp: typ_heap_simps)

  apply (rule c_guard_field_lvalue [rotated])
  apply (fastforce simp: typ_uinfo_t_def)+
  apply (rule c_guard_clift)
  apply (simp add: typ_heap_simps)
done

lemma h_t_valid_and_cslift_and_c_guard_field_mdbNext_CL:
      " \<lbrakk>(s, s') \<in> rf_sr; cte_at' slot s;  valid_mdb' s; cslift s' (Ptr slot) = Some cte'\<rbrakk>
       \<Longrightarrow> (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte')) \<noteq> 0) \<longrightarrow>
           s' \<Turnstile>\<^sub>c ( Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) \<and>
           (\<exists> cten. cslift s' (Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte'))) :: cte_C ptr) = Some cten)  \<and>
           c_guard (Ptr &(Ptr (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte')))::cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr)"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) valid_mdb_ctes_of_next)
  apply (frule (2) rf_sr_cte_relation)
  apply (drule ccte_relation_cmdbnode_relation)
  apply (simp add: mdbNext_not_zero_eq_simpler)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) rf_sr_ctes_of_clift [rotated])+
  apply (clarsimp simp: typ_heap_simps)

  apply (rule c_guard_field_lvalue [rotated])
  apply (fastforce simp: typ_uinfo_t_def)+
  apply (rule c_guard_clift)
  apply (simp add: typ_heap_simps)
done


lemma valid_mdb_Prev_neq_Next_better:
    "\<lbrakk> valid_mdb' s; ctes_of s p = Some cte \<rbrakk> \<Longrightarrow>  mdbPrev (cteMDBNode cte) \<noteq> 0   \<longrightarrow>
     (mdbNext (cteMDBNode cte)) \<noteq> (mdbPrev (cteMDBNode cte))"
  apply (rule impI)
  apply (simp add: valid_mdb'_def)
  apply (simp add: valid_mdb_ctes_def)
  apply (elim conjE)
  apply (drule (1) mdb_chain_0_no_loops)
  apply (simp add: valid_dlist_def)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=cte in allE)
  apply (simp add: Let_def)
  apply clarsimp
  apply (drule_tac s="mdbNext (cteMDBNode cte)" in sym)
  apply simp
  apply (simp add: no_loops_def)
  apply (erule_tac x= "(mdbNext (cteMDBNode cte))" in allE)
  apply (erule notE, rule trancl_trans)
    apply (rule r_into_trancl)
    apply (simp add: mdb_next_unfold)
  apply (rule r_into_trancl)
  apply (simp add: mdb_next_unfold)
done

declare unat_ucast_up_simp[simp]

lemma setIRQState_ccorres:
  "ccorres dc xfdc
          (\<top> and (\<lambda>s. ucast irq \<le> (ucast Kernel_C.maxIRQ :: machine_word)))
          (UNIV \<inter> {s. irqState_' s = irqstate_to_C irqState}
                \<inter> {s. irq_' s = ucast irq})
          []
         (setIRQState irqState irq)
         (Call setIRQState_'proc )"
  apply (rule ccorres_gen_asm)
  apply (cinit simp del: return_bind)
   apply (rule ccorres_symb_exec_l)
      apply simp
      apply (rule_tac r'="dc" and xf'="xfdc" in ccorres_split_nothrow)
          apply (rule_tac P= "\<lambda>s. st = (ksInterruptState s)"
                      and P'= "(UNIV \<inter> {s. irqState_' s = irqstate_to_C irqState}
                                     \<inter> {s. irq_' s = ucast irq}  )"
                   in ccorres_from_vcg)
          apply (rule allI, rule conseqPre, vcg)
          apply (clarsimp simp: setInterruptState_def)
          apply (clarsimp simp: simpler_modify_def)
          apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                carch_state_relation_def cmachine_state_relation_def)
          apply (simp add: cinterrupt_relation_def Kernel_C.maxIRQ_def)
          apply (clarsimp simp: word_sless_msb_less order_le_less_trans
                                unat_ucast_no_overflow_le word_le_nat_alt ucast_ucast_b
                         split: if_split )
          apply ceqv
        apply (ctac add: maskInterrupt_ccorres)
       apply wp
      apply vcg
     apply wp
    apply (simp add: getInterruptState_def gets_def)
    apply wp
   apply (simp add: empty_fail_def getInterruptState_def simpler_gets_def)
  apply clarsimp
  apply (simp add: from_bool_def)
  apply (cases irqState, simp_all)
  apply (simp add: Kernel_C.IRQSignal_def Kernel_C.IRQInactive_def)
  apply (simp add: Kernel_C.IRQTimer_def Kernel_C.IRQInactive_def)
  apply (simp add: Kernel_C.IRQInactive_def Kernel_C.IRQReserved_def)
  done


lemma deletedIRQHandler_ccorres:
  "ccorres dc xfdc
         (\<lambda>s. ucast irq \<le> (ucast Kernel_C.maxIRQ :: machine_word))
         (UNIV \<inter> {s. irq_' s = ucast irq}) []
         (deletedIRQHandler irq)
         (Call deletedIRQHandler_'proc)"
  apply (cinit simp del: return_bind)
  apply (ctac add: setIRQState_ccorres)
  apply clarsimp
done

lemmas ccorres_split_noop_lhs
  = ccorres_split_nothrow[where c=Skip, OF _ ceqv_refl _ _ hoarep.Skip,
    simplified ccorres_seq_skip]

(* FIXME: to SR_Lemmas *)
lemma region_is_bytes_subset:
  "region_is_bytes' ptr sz htd
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> region_is_bytes' ptr' sz' htd"
  by (auto simp: region_is_bytes'_def)

lemma region_actually_is_bytes_subset:
  "region_actually_is_bytes' ptr sz htd
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> region_actually_is_bytes' ptr' sz' htd"
  by (auto simp: region_actually_is_bytes'_def)

lemma intvl_both_le:
  "\<lbrakk> a \<le> x; unat x + y \<le> unat a + b \<rbrakk>
    \<Longrightarrow>  {x ..+ y} \<le> {a ..+ b}"
  apply (rule order_trans[OF _ intvl_sub_offset[where x="x - a"]])
   apply (simp, rule order_refl)
  apply unat_arith
  done

lemma untypedZeroRange_idx_forward_helper:
  "isUntypedCap cap
    \<Longrightarrow> capFreeIndex cap \<le> idx
    \<Longrightarrow> idx \<le> 2 ^ capBlockSize cap
    \<Longrightarrow> valid_cap' cap s
    \<Longrightarrow> (case (untypedZeroRange cap, untypedZeroRange (capFreeIndex_update (\<lambda>_. idx) cap))
       of (Some (a, b), Some (a', b')) \<Rightarrow> {a' ..+ unat (b' + 1 - a')} \<subseteq> {a ..+ unat (b + 1 - a)}
        | _ \<Rightarrow> True)"
  apply (clarsimp split: option.split)
  apply (clarsimp simp: untypedZeroRange_def max_free_index_def Let_def
                        isCap_simps valid_cap_simps' capAligned_def untypedBits_defs
                 split: if_split_asm)
  apply (erule subsetD[rotated], rule intvl_both_le)
   apply (clarsimp simp: getFreeRef_def)
   apply (rule word_plus_mono_right)
    apply (rule PackedTypes.of_nat_mono_maybe_le)
     apply (erule order_le_less_trans, rule power_strict_increasing, simp_all)
   apply (erule is_aligned_no_wrap')
   apply (rule word_of_nat_less, simp)
  apply (simp add: getFreeRef_def)
  apply (simp add: unat_plus_simple[THEN iffD1, OF is_aligned_no_wrap']
                   word_of_nat_less)
  apply (simp add: word_of_nat_le unat_sub
                   order_le_less_trans[OF _ power_strict_increasing]
                   unat_of_nat_eq[where 'a=machine_word_len, folded word_bits_def])
  done

lemma intvl_close_Un:
  "y = x + of_nat n
    \<Longrightarrow> ({x ..+ n} \<union> {y ..+ m}) = {x ..+ n + m}"
  apply ((simp add: intvl_def, safe, simp_all,
    simp_all only: of_nat_add[symmetric]); (rule exI, strengthen refl))
  apply simp_all
  apply (rule ccontr)
  apply (drule_tac x="k - n" in spec)
  apply simp
  done

lemma untypedZeroRange_idx_backward_helper:
  "isUntypedCap cap
    \<Longrightarrow> idx \<le> capFreeIndex cap
    \<Longrightarrow> idx \<le> 2 ^ capBlockSize cap
    \<Longrightarrow> valid_cap' cap s
    \<Longrightarrow> (case untypedZeroRange (capFreeIndex_update (\<lambda>_. idx) cap)
       of None \<Rightarrow> True | Some (a', b') \<Rightarrow>
        {a' ..+ unat (b' + 1 - a')} \<subseteq> {capPtr cap + of_nat idx ..+ (capFreeIndex cap - idx)}
            \<union> (case untypedZeroRange cap
               of Some (a, b) \<Rightarrow> {a ..+ unat (b + 1 - a)}
                | None \<Rightarrow> {})
  )"
  apply (clarsimp split: option.split, intro impI conjI allI)
   apply (rule intvl_both_le; clarsimp simp: untypedZeroRange_def
                         max_free_index_def Let_def
                         isCap_simps valid_cap_simps' capAligned_def
                  split: if_split_asm)
    apply (clarsimp simp: getFreeRef_def)
   apply (clarsimp simp: getFreeRef_def)
   apply (simp add: word_of_nat_le unat_sub
                    order_le_less_trans[OF _ power_strict_increasing]
                    unat_of_nat_eq[where 'a=machine_word_len, folded word_bits_def])
  apply (subst intvl_close_Un)
   apply (clarsimp simp: untypedZeroRange_def
                         max_free_index_def Let_def
                         getFreeRef_def
                  split: if_split_asm)
  apply (clarsimp simp: untypedZeroRange_def
                        max_free_index_def Let_def
                        getFreeRef_def isCap_simps valid_cap_simps'
                 split: if_split_asm)
  apply (simp add: word_of_nat_le unat_sub capAligned_def
                   order_le_less_trans[OF _ power_strict_increasing]
                   order_le_less_trans[where x=idx]
                   unat_of_nat_eq[where 'a=machine_word_len, folded word_bits_def])
  done

lemma ctes_of_untyped_zero_rf_sr_case:
  "\<lbrakk> ctes_of s p = Some cte; (s, s') \<in> rf_sr;
      untyped_ranges_zero' s \<rbrakk>
    \<Longrightarrow> case untypedZeroRange (cteCap cte)
               of None \<Rightarrow> True
    | Some (start, end) \<Rightarrow> region_actually_is_zero_bytes start (unat ((end + 1) - start)) s'"
  by (simp split: option.split add: ctes_of_untyped_zero_rf_sr)

lemma gsUntypedZeroRanges_update_helper:
  "(\<sigma>, s) \<in> rf_sr
    \<Longrightarrow> (zero_ranges_are_zero (gsUntypedZeroRanges \<sigma>) (t_hrs_' (globals s))
            \<longrightarrow> zero_ranges_are_zero (f (gsUntypedZeroRanges \<sigma>)) (t_hrs_' (globals s)))
    \<Longrightarrow> (gsUntypedZeroRanges_update f \<sigma>, s) \<in> rf_sr"
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

lemma heap_list_zero_Ball_intvl:
  "heap_list_is_zero hmem ptr n = (\<forall>x \<in> {ptr ..+ n}. hmem x = 0)"
  apply safe
   apply (erule heap_list_h_eq_better)
   apply (simp add: heap_list_rpbs)
  apply (rule trans[OF heap_list_h_eq2 heap_list_rpbs])
  apply simp
  done

lemma untypedZeroRange_not_device:
  "untypedZeroRange cap = Some r
    \<Longrightarrow> \<not> capIsDevice cap"
  by (clarsimp simp: untypedZeroRange_def)

lemma updateTrackedFreeIndex_noop_ccorres:
  "ccorres dc xfdc (cte_wp_at' ((\<lambda>cap. isUntypedCap cap
              \<and> idx \<le> 2 ^ capBlockSize cap
              \<and> (capFreeIndex cap \<le> idx \<or> cap' = cap)) o cteCap) slot
          and valid_objs' and untyped_ranges_zero')
      {s. \<not> capIsDevice cap' \<longrightarrow> region_actually_is_zero_bytes (capPtr cap' + of_nat idx) (capFreeIndex cap' - idx) s} hs
      (updateTrackedFreeIndex slot idx) Skip"
  (is "ccorres dc xfdc ?P ?P' _ _ _")
  apply (simp add: updateTrackedFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_getCTE[where P="\<lambda>rv.
        cte_wp_at' ((=) rv) slot and ?P" and P'="K ?P'"])
    apply (rule ccorres_from_vcg)
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (frule(1) ctes_of_valid')
    apply (frule(2) ctes_of_untyped_zero_rf_sr_case)
    apply (clarsimp simp: simpler_modify_def bind_def cte_wp_at_ctes_of)
    apply (erule gsUntypedZeroRanges_update_helper)
    apply (clarsimp simp: zero_ranges_are_zero_def
                   split: if_split)
    apply (case_tac "(a, b) \<in> gsUntypedZeroRanges \<sigma>")
     apply (drule(1) bspec, simp)
    apply (erule disjE_L)
     apply (frule(3) untypedZeroRange_idx_forward_helper)
     apply (clarsimp simp: isCap_simps valid_cap_simps')
     apply (case_tac "untypedZeroRange (cteCap cte)")
      apply (clarsimp simp: untypedZeroRange_def
                       valid_cap_simps'
                       max_free_index_def Let_def
                     split: if_split_asm)
     apply clarsimp
     apply (thin_tac "\<not> capIsDevice cap' \<longrightarrow> P" for P)
     apply (clarsimp split: option.split_asm)
     apply (subst region_actually_is_bytes_subset, simp+)
     apply (subst heap_list_is_zero_mono2, simp+)
    apply (frule untypedZeroRange_idx_backward_helper[where idx=idx],
      simp+)
    apply (clarsimp simp: isCap_simps valid_cap_simps')
    apply (clarsimp split: option.split_asm)
     apply (clarsimp dest!: untypedZeroRange_not_device)
     apply (subst region_actually_is_bytes_subset, simp+)
     apply (subst heap_list_is_zero_mono2, simp+)
    apply (simp add: region_actually_is_bytes'_def heap_list_zero_Ball_intvl)
    apply (clarsimp dest!: untypedZeroRange_not_device)
    apply blast
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply clarsimp
  done

lemma updateTrackedFreeIndex_forward_noop_ccorres:
  "ccorres dc xfdc (cte_wp_at' ((\<lambda>cap. isUntypedCap cap
              \<and> capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap) o cteCap) slot
          and valid_objs' and untyped_ranges_zero') UNIV hs
      (updateTrackedFreeIndex slot idx) Skip"
  (is "ccorres dc xfdc ?P UNIV _ _ _")
  apply (rule ccorres_name_pre)
   apply (rule ccorres_guard_imp2,
     rule_tac cap'="cteCap (the (ctes_of s slot))" in updateTrackedFreeIndex_noop_ccorres)
  apply (clarsimp simp: cte_wp_at_ctes_of region_actually_is_bytes'_def)
  done

lemma clearUntypedFreeIndex_noop_ccorres:
  "ccorres dc xfdc (valid_objs' and untyped_ranges_zero') UNIV hs
      (clearUntypedFreeIndex p) Skip"
  apply (simp add: clearUntypedFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_getCTE[where P="\<lambda>rv. cte_wp_at' ((=) rv) p
        and valid_objs' and untyped_ranges_zero'" and P'="K UNIV"])
    apply (case_tac "cteCap cte", simp_all add: ccorres_guard_imp[OF ccorres_return_Skip])[1]
    apply (rule ccorres_guard_imp, rule updateTrackedFreeIndex_forward_noop_ccorres)
     apply (clarsimp simp: cte_wp_at_ctes_of max_free_index_def)
     apply (frule(1) Finalise_R.ctes_of_valid')
     apply (clarsimp simp: valid_cap_simps')
    apply simp
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply simp
  done

lemma canonical_address_mdbNext_CL:
  "canonical_address (mdbNext_CL (mdb_node_lift (cteMDBNode_C cte')))"
  by (simp add: mdb_node_lift_def canonical_address_sign_extended sign_extended_sign_extend
                canonical_bit_def)

lemma canonical_address_mdbNext':
  "ccte_relation cte cte' \<Longrightarrow> canonical_address (mdbNext (cteMDBNode cte))"
  apply (rule rsubst[where P=canonical_address, OF canonical_address_mdbNext_CL])
  apply (rule cmdb_node_relation_mdbNext)
  apply (erule ccte_relation_cmdbnode_relation)
  done

lemma canonical_address_mdbNext:
  "\<lbrakk> (s, s') \<in> rf_sr; ctes_of s slot = Some cte \<rbrakk> \<Longrightarrow> canonical_address (mdbNext (cteMDBNode cte))"
  apply (drule cmap_relation_cte)
  apply (erule (1) cmap_relationE1)
  apply (erule canonical_address_mdbNext')
  done

definition
  arch_cleanup_info_wf' :: "arch_capability \<Rightarrow> bool"
where
  "arch_cleanup_info_wf' acap \<equiv> True"

definition
  cleanup_info_wf' :: "capability \<Rightarrow> bool"
where
  "cleanup_info_wf' cap \<equiv> case cap of
      IRQHandlerCap irq \<Rightarrow>
        UCAST(6\<rightarrow>machine_word_len) irq \<le>  SCAST(32 signed\<rightarrow>machine_word_len) Kernel_C.maxIRQ
    | ArchObjectCap acap \<Rightarrow> arch_cleanup_info_wf' acap
    | _ \<Rightarrow> True"

(* FIXME: move *)
lemma hrs_mem_update_compose:
  "hrs_mem_update f (hrs_mem_update g h) = hrs_mem_update (f \<circ> g) h"
  by (auto simp: hrs_mem_update_def split: prod.split)

(* FIXME: move *)
lemma packed_heap_update_collapse':
  fixes p :: "'a::packed_type ptr"
  shows "heap_update p v \<circ> heap_update p u = heap_update p v"
  by (auto simp: packed_heap_update_collapse)

(* FIXME: move *)
lemma access_array_from_elements:
  fixes v :: "'a::packed_type['b::finite]"
  assumes "\<forall>i < CARD('b). h_val h (array_ptr_index p False i) = v.[i]"
  shows "h_val h p = v"
  by (rule cart_eq[THEN iffD2]) (simp add: assms heap_access_Array_element')

(* FIXME: move *)
lemma h_val_foldr_heap_update:
  fixes v :: "'i \<Rightarrow> 'a::mem_type"
  assumes "\<forall>x y. {x,y} \<subseteq> set xs \<longrightarrow> x \<noteq> y \<longrightarrow> ptr_span (p x) \<inter> ptr_span (p y) = {}"
  assumes "distinct xs" "i \<in> set xs"
  shows "h_val (foldr (\<lambda>i. heap_update (p i) (v i)) xs h) (p i) = v i"
  using assms by (induct xs arbitrary: h;
                  fastforce simp: h_val_heap_update h_val_update_regions_disjoint)

(* FIXME: move *)
lemma ptr_span_array_ptr_index_disjoint:
  fixes p :: "('a::packed_type['b::finite]) ptr"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  assumes b: "x < CARD('b)" "y < CARD('b)"
  assumes n: "x \<noteq> y"
  shows "ptr_span (array_ptr_index p False x) \<inter> ptr_span (array_ptr_index p False y) = {}"
  proof -
    have l: "CARD('b) * size_of TYPE('a) \<le> 2 ^ LENGTH(64)" using s by simp
    have p: "\<And>x k. x < CARD('b) \<Longrightarrow> k < size_of TYPE('a)
                      \<Longrightarrow> x * size_of TYPE('a) + k < 2 ^ LENGTH(64)"
      by (metis less_le_trans[OF _ l] less_imp_not_less mod_lemma mult.commute nat_mod_lem neq0_conv)
    show ?thesis
      apply (clarsimp simp: array_ptr_index_def ptr_add_def intvl_disj_offset)
      apply (rule disjointI)
      apply (clarsimp simp: intvl_def)
      apply (subst (asm) of_nat_mult[symmetric])+
      apply (subst (asm) of_nat_add[symmetric])+
      apply (subst (asm) of_nat_inj[OF p p]; (simp add: b)?)
      apply (drule arg_cong[where f="\<lambda>x. x div size_of TYPE('a)"]; simp add: n)
      done
  qed

(* FIXME: move *)
lemma h_val_heap_update_Array:
  fixes v :: "'a::packed_type['b::finite]"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  shows "h_val (heap_update p v h) p = v"
  apply (rule access_array_from_elements)
  apply (clarsimp simp: heap_update_Array foldl_conv_foldr)
  apply (rule h_val_foldr_heap_update; clarsimp simp: ptr_span_array_ptr_index_disjoint[OF s])
  done

(* FIXME: move *)
lemma foldr_heap_update_commute:
  assumes "\<forall>y. y \<in> set xs \<longrightarrow> ptr_span q \<inter> ptr_span (p y) = {}"
  shows "foldr (\<lambda>i. heap_update (p i) (v i)) xs (heap_update q u h)
           = heap_update q u (foldr (\<lambda>i. heap_update (p i) (v i)) xs h)"
  using assms by (induct xs) (auto simp: LemmaBucket_C.heap_update_commute)

(* FIXME: move *)
lemma foldr_packed_heap_update_collapse:
  fixes u v :: "'i \<Rightarrow> 'a::packed_type"
  assumes "\<forall>x y. {x,y} \<subseteq> set xs \<longrightarrow> y \<noteq> x \<longrightarrow> ptr_span (p x) \<inter> ptr_span (p y) = {}"
  assumes "distinct xs"
  shows "foldr (\<lambda>i. heap_update (p i) (v i)) xs (foldr (\<lambda>i. heap_update (p i) (u i)) xs h)
           = foldr (\<lambda>i. heap_update (p i) (v i)) xs h"
  using assms
  apply -
  apply (induct xs arbitrary: h; clarsimp; rename_tac x xs h)
  apply (drule_tac x=x in spec; clarsimp)
  apply (subst foldr_heap_update_commute; clarsimp simp: packed_heap_update_collapse)
  apply (drule_tac x=y in spec; clarsimp)
  done

(* FIXME: move *)
lemma packed_Array_heap_update_collapse:
  fixes p :: "('a::packed_type['b::finite]) ptr"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  shows "heap_update p v (heap_update p u h) = heap_update p v h"
  by (simp add: heap_update_Array foldl_conv_foldr foldr_packed_heap_update_collapse
                ptr_span_array_ptr_index_disjoint[OF s])

(* FIXME: move *)
lemma packed_Array_heap_update_collapse':
  fixes p :: "('a::packed_type['b::finite]) ptr"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  shows "heap_update p v \<circ> heap_update p u = heap_update p v"
  by (auto simp: packed_Array_heap_update_collapse[OF s])

(* FIXME: move *)
definition
  heap_modify :: "'a::c_type ptr \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> heap_mem \<Rightarrow> heap_mem"
where
  "heap_modify p f \<equiv> \<lambda>h. heap_update p (f (h_val h p)) h"

(* FIXME: move *)
lemma heap_modify_def2:
  "heap_modify (p::'a::c_type ptr) f \<equiv>
    \<lambda>h. let bytes = heap_list h (size_of TYPE('a)) (ptr_val p) in
          heap_update_list (ptr_val p) (to_bytes (f (from_bytes bytes)) bytes) h"
  by (simp add: heap_modify_def Let_def heap_update_def h_val_def)

(* FIXME: move *)
lemma heap_modify_compose:
  fixes p :: "'a::packed_type ptr"
  shows "heap_modify p f \<circ> heap_modify p g = heap_modify p (f \<circ> g)"
    and "heap_modify p f (heap_modify p g h) = heap_modify p (f \<circ> g) h"
  by (auto simp: heap_modify_def h_val_heap_update packed_heap_update_collapse)

(* FIXME: move *)
lemma heap_modify_compose_Array:
  fixes p :: "('a::packed_type['b::finite]) ptr"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  shows "heap_modify p f \<circ> heap_modify p g = heap_modify p (f \<circ> g)"
    and "heap_modify p f (heap_modify p g h) = heap_modify p (f \<circ> g) h"
  by (auto simp: heap_modify_def h_val_heap_update_Array[OF s]
                 packed_Array_heap_update_collapse[OF s])

(* FIXME: move *)
lemma fold_heap_modify_commute:
  fixes p :: "'a::packed_type ptr"
  shows "fold (heap_modify p \<circ> f) upds = heap_modify p (fold f upds)"
  apply (induction upds)
   apply (simp add: heap_modify_def heap_update_id)
  apply (clarsimp simp: heap_modify_compose[THEN fun_cong, simplified] o_def)
  done

(* FIXME: move *)
lemma fold_heap_modify_commute_Array:
  fixes p :: "('a::packed_type['b::finite]) ptr"
  assumes s: "CARD('b) * size_of TYPE('a) \<le> 2 ^ addr_bitsize"
  shows "fold (heap_modify p \<circ> f) upds = heap_modify p (fold f upds)"
  apply (induction upds)
   apply (simp add: heap_modify_def heap_update_id_Array)
  apply (clarsimp simp: heap_modify_compose_Array[OF s, THEN fun_cong, simplified] o_def)
  done

definition
  word_set_or_clear :: "bool \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word"
where
  "word_set_or_clear s p w \<equiv> if s then w || p else w && ~~ p"

(* FIXME: move *)
lemma whileAnno_subst_invariant:
  "whileAnno b I' V c = whileAnno b I V c"
  by (simp add: whileAnno_def)

lemma hoarep_conseq_spec_state:
  fixes \<Gamma> :: "'p \<Rightarrow> ('s,'p,'f) com option"
  assumes "\<forall>\<sigma>. \<Gamma> \<turnstile> {s. s = \<sigma> \<and> P s} c (Q \<sigma>)"
  assumes "\<forall>\<sigma>. \<sigma> \<in> P' \<longrightarrow> P \<sigma> \<and> Q \<sigma> \<subseteq> Q'"
  shows "\<Gamma> \<turnstile> P' c Q'"
  using assms by (fastforce intro: hoarep.Conseq)

lemma hrs_simps:
  "hrs_mem (mem, htd) = mem"
  "hrs_mem_update f (mem, htd) = (f mem, htd)"
  "hrs_htd (mem, htd) = htd"
  "hrs_htd_update g (mem, htd) = (mem, g htd)"
  by (auto simp: hrs_mem_def hrs_mem_update_def hrs_htd_def hrs_htd_update_def)

lemma clift_heap_modify_same:
  fixes p :: "'a :: mem_type ptr"
  assumes "hrs_htd hp \<Turnstile>\<^sub>t p"
  assumes "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
  shows "clift (hrs_mem_update (heap_modify p f) hp) = (clift hp :: 'b :: mem_type typ_heap)"
  using assms unfolding hrs_mem_update_def
  apply (cases hp)
  apply (simp add: split_def hrs_htd_def heap_modify_def)
  apply (erule lift_t_heap_update_same)
  apply simp
  done

lemma zero_ranges_are_zero_modify[simp]:
  "h_t_valid (hrs_htd hrs) c_guard (ptr :: 'a ptr)
    \<Longrightarrow> typ_uinfo_t TYPE('a :: wf_type) \<noteq> typ_uinfo_t TYPE(word8)
    \<Longrightarrow> zero_ranges_are_zero rs (hrs_mem_update (heap_modify ptr f) hrs)
        = zero_ranges_are_zero rs hrs"
  apply (clarsimp simp: zero_ranges_are_zero_def hrs_mem_update
                intro!: ball_cong[OF refl] conj_cong[OF refl])
  apply (drule region_actually_is_bytes)
  apply (drule(2) region_is_bytes_disjoint)
  apply (simp add: heap_modify_def heap_update_def heap_list_update_disjoint_same Int_commute)
  done

lemma h_val_heap_modify:
  fixes p :: "'a::mem_type ptr"
  shows "h_val (heap_modify p f h) p = f (h_val h p)"
  by (simp add: heap_modify_def h_val_heap_update)

lemma array_fupdate_index:
  fixes arr :: "'a::c_type['b::finite]"
  assumes "i < CARD('b)" "j < CARD('b)"
  shows "fupdate i f arr.[j] = (if i = j then f (arr.[i]) else arr.[j])"
  using assms by (cases "i = j"; simp add: fupdate_def)

lemma foldl_map_pair_constant:
  "foldl (\<lambda>acc p. f acc (fst p) (snd p)) z (map (\<lambda>x. (x,v)) xs) = foldl (\<lambda>acc x. f acc x v) z xs"
  by (induct xs arbitrary: z) auto

lemma word_set_or_clear_test_bit:
  fixes w :: "'a::len word"
  shows "i < LENGTH('a) \<Longrightarrow> word_set_or_clear b p w !! i = (if p !! i then b else w !! i)"
  by (auto simp: word_set_or_clear_def word_ops_nth_size word_size split: if_splits)

lemma heap_modify_fold:
  "heap_update p (f (h_val h p)) h = heap_modify p f h"
  by (simp add: heap_modify_def)

lemma fold_array_update_index:
  fixes arr :: "'a::c_type['b::finite]"
  assumes "i < CARD('b)"
  shows "fold (\<lambda>i arr. Arrays.update arr i (f i)) is arr.[i] = (if i \<in> set is then f i else arr.[i])"
  using assms by (induct "is" arbitrary: arr) (auto split: if_splits)

lemma t_hrs_'_update_heap_modify_fold:
  "gs\<lparr> t_hrs_' := hrs_mem_update (heap_update p (f (h_val (hrs_mem (t_hrs_' gs)) p))) (t_hrs_' gs) \<rparr>
    = t_hrs_'_update (hrs_mem_update (heap_modify p f)) gs"
  by (clarsimp simp: heap_modify_def hrs_mem_update_def hrs_mem_def split: prod.splits)

lemma heap_modify_Array_element:
  fixes p :: "'a::packed_type ptr"
  fixes p' :: "('a['b::finite]) ptr"
  assumes "p = ptr_coerce p' +\<^sub>p int n"
  assumes "n < CARD('b)"
  assumes "CARD('b) * size_of TYPE('a) < 2 ^ addr_bitsize"
  shows "heap_modify p f = heap_modify p' (fupdate n f)"
  using assms by (simp add: heap_access_Array_element heap_update_Array_element'
                            heap_modify_def fupdate_def)

lemma fupdate_word_set_or_clear_max_word:
  "fupdate i (word_set_or_clear b max_word) arr = Arrays.update arr i (if b then max_word else 0)"
  by (simp add: fupdate_def word_set_or_clear_def)

lemma h_t_valid_Array_element':
  "\<lbrakk> htd \<Turnstile>\<^sub>t (p :: (('a :: mem_type)['b :: finite]) ptr); 0 \<le> n; n < CARD('b) \<rbrakk>
    \<Longrightarrow> htd \<Turnstile>\<^sub>t ((ptr_coerce p :: 'a ptr) +\<^sub>p n)"
  apply (drule_tac n="nat n" and coerce=False in h_t_valid_Array_element')
   apply simp
  apply (simp add: array_ptr_index_def)
  done

lemma Arch_postCapDeletion_ccorres:
  "ccorres dc xfdc
     (\<top> and (\<lambda>s. arch_cleanup_info_wf' acap))
     (UNIV \<inter> {s. ccap_relation (ArchObjectCap acap) (cap_' s)}) hs
     (RISCV64_H.postCapDeletion acap)
     (Call Arch_postCapDeletion_'proc)"
  apply (cinit lift: cap_')
   apply (rule ccorres_return_Skip)
  apply simp
  done

lemma not_irq_or_arch_cap_case:
  "\<lbrakk>\<not>isIRQHandlerCap cap; \<not> isArchCap \<top> cap\<rbrakk> \<Longrightarrow>
    (case cap of IRQHandlerCap irq \<Rightarrow> f irq | ArchObjectCap acap \<Rightarrow> g acap | _ \<Rightarrow> h) = h"
  by (case_tac cap; clarsimp simp: isCap_simps)

lemma postCapDeletion_ccorres:
  "cleanup_info_wf' cap \<Longrightarrow>
   ccorres dc xfdc
      \<top> (UNIV \<inter> {s. ccap_relation cap (cap_' s)}) hs
     (postCapDeletion cap)
     (Call postCapDeletion_'proc)"
  supply Collect_const[simp del]
  apply (cinit lift: cap_' simp: Retype_H.postCapDeletion_def)
   apply csymbr
   apply (clarsimp simp: cap_get_tag_isCap)
   apply (rule ccorres_Cond_rhs)
    apply (clarsimp simp: isCap_simps )
    apply (rule ccorres_symb_exec_r)
      apply (rule_tac xf'=irq_' in ccorres_abstract, ceqv)
      apply (rule_tac P="rv' = ucast (capIRQ cap)" in ccorres_gen_asm2)
      apply (fold dc_def)
      apply (frule cap_get_tag_to_H, solves \<open>clarsimp simp: cap_get_tag_isCap_unfolded_H_cap\<close>)
      apply (clarsimp simp: cap_irq_handler_cap_lift)
      apply (ctac(no_vcg) add: deletedIRQHandler_ccorres)
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply csymbr
   apply (clarsimp simp: cap_get_tag_isCap)
   apply (rule ccorres_Cond_rhs)
    apply (wpc; clarsimp simp: isCap_simps)
    apply (ctac(no_vcg) add: Arch_postCapDeletion_ccorres[unfolded dc_def])
   apply (simp add: not_irq_or_arch_cap_case)
   apply (rule ccorres_return_Skip[unfolded dc_def])+
  apply clarsimp
  apply (rule conjI, clarsimp simp: isCap_simps  Kernel_C.maxIRQ_def)
   apply (frule cap_get_tag_isCap_unfolded_H_cap(5))
   apply (clarsimp simp: cap_irq_handler_cap_lift ccap_relation_def cap_to_H_def
                         cleanup_info_wf'_def maxIRQ_def Kernel_C.maxIRQ_def)
(*   apply word_bitwise *)
  apply (rule conjI, clarsimp simp: isCap_simps cleanup_info_wf'_def)
  apply (rule conjI[rotated], clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(5))
  apply (clarsimp simp: cap_irq_handler_cap_lift ccap_relation_def cap_to_H_def
                        cleanup_info_wf'_def c_valid_cap_def cl_valid_cap_def mask_def)
  apply (rule mask_eq_ucast_eq[where 'a="6" and 'b="64" and 'c="64", symmetric, simplified])
  by (simp add: mask_def)

lemma emptySlot_ccorres:
  "ccorres dc xfdc
          (valid_mdb' and valid_objs' and pspace_aligned' and untyped_ranges_zero')
          (UNIV \<inter> {s. slot_' s = Ptr slot}
                \<inter> {s. ccap_relation info (cleanupInfo_' s) \<and> cleanup_info_wf' info}  )
          []
          (emptySlot slot info)
          (Call emptySlot_'proc)"
  apply (cinit lift: slot_' cleanupInfo_' simp: case_Null_If)

  \<comment> \<open>--- handle the clearUntypedFreeIndex\<close>
   apply (rule ccorres_split_noop_lhs, rule clearUntypedFreeIndex_noop_ccorres)

  \<comment> \<open>--- instruction: newCTE \<leftarrow> getCTE slot;                 ---\<close>
    apply (rule ccorres_pre_getCTE)
  \<comment> \<open>--- instruction: CALL on C side\<close>
    apply (rule ccorres_move_c_guard_cte)
    apply csymbr
    apply (rule ccorres_abstract_cleanup)
    apply (rename_tac cap_tag)
    apply (rule_tac P="(cap_tag = scast cap_null_cap)
          = (cteCap newCTE = NullCap)" in ccorres_gen_asm2)
    apply (simp del: Collect_const)

   \<comment> \<open>--- instruction: if-then-else / IF-THEN-ELSE\<close>
    apply (rule ccorres_cond2'[where R=\<top>])

    \<comment> \<open>*** link between abstract and concrete conditionals ***\<close>
      apply (clarsimp split: if_split)

    \<comment> \<open>*** proof for the 'else' branch (return () and SKIP) ***\<close>
     prefer 2
     apply (ctac add: ccorres_return_Skip[unfolded dc_def])

    \<comment> \<open>*** proof for the 'then' branch ***\<close>

    \<comment> \<open>---instructions: multiple on C side, including mdbNode fetch\<close>
    apply (rule ccorres_rhs_assoc)+
              \<comment> \<open>we have to do it here because the first assoc did not apply inside the then block\<close>
    apply (rule ccorres_move_c_guard_cte | csymbr)+
    apply (rule ccorres_symb_exec_r)
      apply (rule_tac xf'="mdbNode_'" in ccorres_abstract, ceqv)
      apply (rename_tac "cmdbNode")
      apply (rule_tac P="cmdbnode_relation (cteMDBNode newCTE) cmdbNode"
        in ccorres_gen_asm2)
      apply csymbr+

      \<comment> \<open>--- instruction: updateMDB (mdbPrev rva) (mdbNext_update \<dots>) but with Ptr\<dots>\<noteq> NULL on C side\<close>
      apply (simp only:Ptr_not_null_pointer_not_zero) \<comment> \<open>replaces Ptr p \<noteq> NULL with p\<noteq>0\<close>

      \<comment> \<open>--- instruction: y \<leftarrow> updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva))\<close>
      apply (ctac (no_simp, no_vcg) pre:ccorres_move_guard_ptr_safe
        add: updateMDB_mdbPrev_set_mdbNext)
            \<comment> \<open>here ctac alone does not apply because the subgoal generated
                by the rule are not solvable by simp\<close>
            \<comment> \<open>so we have to use (no_simp) (or apply (rule ccorres_split_nothrow))\<close>
          apply (simp add: cmdbnode_relation_def)
         apply assumption
      \<comment> \<open>*** Main goal ***\<close>
      \<comment> \<open>--- instruction: updateMDB (mdbNext rva)
                    (\<lambda>mdb. mdbFirstBadged_update (\<lambda>_. mdbFirstBadged mdb \<or> mdbFirstBadged rva)
                            (mdbPrev_update (\<lambda>_. mdbPrev rva) mdb));\<close>
        apply (rule ccorres_rhs_assoc2 )  \<comment> \<open>to group the 2 first C instrutions together\<close>
        apply (ctac (no_vcg) add: emptySlot_helper)

      \<comment> \<open>--- instruction:  y \<leftarrow> updateCap slot capability.NullCap;\<close>
          apply (simp del: Collect_const)
          apply csymbr
            apply (ctac (no_vcg) pre:ccorres_move_guard_ptr_safe)
            apply csymbr
            apply (rule ccorres_move_c_guard_cte)
                \<comment> \<open>--- instruction y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);\<close>
                apply (ctac (no_vcg) pre: ccorres_move_guard_ptr_safe
                  add: ccorres_updateMDB_const [unfolded const_def])

                  \<comment> \<open>the post_cap_deletion case\<close>

                  apply (ctac(no_vcg) add: postCapDeletion_ccorres [unfolded dc_def])

                \<comment> \<open>Haskell pre/post for y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);\<close>
                 apply wp
                \<comment> \<open>C       pre/post for y \<leftarrow> updateMDB slot (\<lambda>a. nullMDBNode);\<close>
                apply simp
              \<comment> \<open>C pre/post for the 2nd CALL\<close>
            \<comment> \<open>Haskell pre/post for y \<leftarrow> updateCap slot capability.NullCap;\<close>
             apply wp
            \<comment> \<open>C       pre/post for y \<leftarrow> updateCap slot capability.NullCap;\<close>
            apply (simp add: Collect_const_mem cmdbnode_relation_def mdb_node_to_H_def nullMDBNode_def false_def)
        \<comment> \<open>Haskell pre/post for the two nested updates\<close>
         apply wp
        \<comment> \<open>C       pre/post for the two nested updates\<close>
        apply (simp add: Collect_const_mem ccap_relation_NullCap_iff)
      \<comment> \<open>Haskell pre/post for  (updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva)))\<close>
       apply (simp, wp)
      \<comment> \<open>C       pre/post for  (updateMDB (mdbPrev rva) (mdbNext_update (\<lambda>_. mdbNext rva)))\<close>
      apply simp+
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply simp
   apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)

  \<comment> \<open>final precondition proof\<close>
  apply (clarsimp simp: typ_heap_simps Collect_const_mem
                        cte_wp_at_ctes_of)

  apply (rule conjI)
   \<comment> \<open>Haskell side\<close>
   apply (simp add: is_aligned_3_next canonical_address_mdbNext)

  \<comment> \<open>C side\<close>
  apply (clarsimp simp: map_comp_Some_iff typ_heap_simps)
  apply (subst cap_get_tag_isCap)
   apply (rule ccte_relation_ccap_relation)
   apply (simp add: ccte_relation_def c_valid_cte_def
                    cl_valid_cte_def c_valid_cap_def)
  apply simp
  done


(************************************************************************)
(*                                                                      *)
(* capSwapForDelete_ccorres *********************************************)
(*                                                                      *)
(************************************************************************)

lemma ccorres_return_void_C:
  "ccorres dc xfdc \<top> UNIV (SKIP # hs) (return rv) (return_void_C)"
  apply (rule ccorres_from_vcg_throws)
  apply (simp add: return_def)
  apply (rule allI, rule conseqPre)
  apply vcg
  apply simp
  done

declare Collect_const [simp del]

lemma capSwapForDelete_ccorres:
  "ccorres dc xfdc
          (valid_mdb' and pspace_aligned' and pspace_canonical')
          (UNIV \<inter> {s. slot1_' s = Ptr slot1}
                \<inter> {s. slot2_' s = Ptr slot2})
          []
          (capSwapForDelete slot1 slot2)
          (Call capSwapForDelete_'proc)"
  apply (cinit lift: slot1_' slot2_' simp del: return_bind)
  \<comment> \<open>***Main goal***\<close>
  \<comment> \<open>--- instruction: when (slot1 \<noteq> slot2) \<dots> / IF Ptr slot1 = Ptr slot2 THEN \<dots>\<close>
   apply (simp add:when_def)
   apply (rule ccorres_if_cond_throws2 [where Q = \<top> and Q' = \<top>])
      apply (case_tac "slot1=slot2", simp+)
     apply (rule ccorres_return_void_C [simplified dc_def])

  \<comment> \<open>***Main goal***\<close>
  \<comment> \<open>--- ccorres goal with 2 affectations (cap1 and cap2) on both on Haskell and C\<close>
  \<comment> \<open>---   \<Longrightarrow> execute each part independently\<close>
    apply (simp add: liftM_def cong: call_ignore_cong)
    apply (rule ccorres_pre_getCTE)+
    apply (rule ccorres_move_c_guard_cte, rule ccorres_symb_exec_r)+
  \<comment> \<open>***Main goal***\<close>
        apply (ctac (no_vcg) add: cteSwap_ccorres [unfolded dc_def] )
       \<comment> \<open>C Hoare triple for \<acute>cap2 :== \<dots>\<close>
       apply vcg
       \<comment> \<open>C existential Hoare triple for \<acute>cap2 :== \<dots>\<close>
      apply simp
      apply (rule conseqPre)
       apply vcg
      apply simp
     \<comment> \<open>C Hoare triple for \<acute>cap1 :== \<dots>\<close>
     apply vcg
     \<comment> \<open>C existential Hoare triple for \<acute>cap1 :== \<dots>\<close>
    apply simp
    apply (rule conseqPre)
     apply vcg
    apply simp

  \<comment> \<open>Hoare triple for return_void\<close>
   apply vcg

  \<comment> \<open>***Generalized preconditions***\<close>
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of map_comp_Some_iff
    typ_heap_simps ccap_relation_def)
  apply (simp add: cl_valid_cte_def c_valid_cap_def)
done



declare Collect_const [simp add]

(************************************************************************)
(*                                                                      *)
(* Arch_sameRegionAs_ccorres ********************************************)
(*                                                                      *)
(************************************************************************)

lemma cap_get_tag_PageCap_frame:
  "ccap_relation cap cap' \<Longrightarrow>
   (cap_get_tag cap' = scast cap_frame_cap) =
   (cap =
    capability.ArchObjectCap
     (FrameCap (cap_frame_cap_CL.capFBasePtr_CL (cap_frame_cap_lift cap'))
              (vmrights_to_H (cap_frame_cap_CL.capFVMRights_CL (cap_frame_cap_lift cap')))
              (framesize_to_H (capFSize_CL (cap_frame_cap_lift cap')))
              (to_bool (cap_frame_cap_CL.capFIsDevice_CL (cap_frame_cap_lift cap')))
    (if cap_frame_cap_CL.capFMappedASID_CL (cap_frame_cap_lift cap') = 0
     then None else
     Some ((cap_frame_cap_CL.capFMappedASID_CL (cap_frame_cap_lift cap')),
          cap_frame_cap_CL.capFMappedAddress_CL (cap_frame_cap_lift cap')))))"
  apply (rule iffI)
   apply (erule ccap_relationE)
   apply (clarsimp simp add: cap_lifts cap_to_H_def Let_def  split: if_split)
  apply (simp add: cap_get_tag_isCap isCap_simps frameSize_def)
done

lemma fff_is_pageBits:
  "(0xFFF :: machine_word) = 2 ^ pageBits - 1"
  by (simp add: pageBits_def)


(* used? *)
lemma valid_cap'_PageCap_is_aligned:
  "valid_cap' (ArchObjectCap (arch_capability.FrameCap w r sz d option)) t  \<Longrightarrow>
  is_aligned w (pageBitsForSize sz)"
  apply (simp add: valid_cap'_def capAligned_def)
done

lemma Arch_sameRegionAs_spec:
  notes cap_get_tag = ccap_rel_cap_get_tag_cases_arch'
  shows
    "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>  ccap_relation (ArchObjectCap capa) \<acute>cap_a \<and>
                   ccap_relation (ArchObjectCap capb) \<acute>cap_b  \<rbrace>
    Call Arch_sameRegionAs_'proc
    \<lbrace>  \<acute>ret__unsigned_long = from_bool (Arch.sameRegionAs capa capb) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (simp add: RISCV64_H.sameRegionAs_def)
  subgoal for capa capb cap_b cap_a
    apply (cases capa; cases capb;
           frule (1) cap_get_tag[where cap'=cap_a]; (frule cap_lifts[where c=cap_a, THEN iffD1])?;
           frule (1) cap_get_tag[where cap'=cap_b]; (frule cap_lifts[where c=cap_b, THEN iffD1])?)
                   apply (simp_all add: cap_tag_defs isCap_simps from_bool_def true_def false_def if_0_1_eq)
      apply (all \<open>clarsimp simp: ccap_relation_def cap_to_H_def
                             c_valid_cap_def cl_valid_cap_def Let_def\<close>)
    apply (clarsimp simp: cap_frame_cap_lift_def'[simplified cap_tag_defs]
                          framesize_to_H_def pageBitsForSize_def field_simps
                          pageBits_def ptTranslationBits_def
                          RISCV_4K_Page_def RISCV_Mega_Page_def RISCV_Giga_Page_def
                   split: vmpage_size.splits if_splits)
    sorry (* FIXME RISCV: potential state relation / spec issue, 36 subgoals;
                          doesn't look like this made much progress *)
  done

(* combination of cap_get_capSizeBits + cap_get_archCapSizeBits from C *)
definition
  get_capSizeBits_CL :: "cap_CL option \<Rightarrow> nat" where
  "get_capSizeBits_CL \<equiv> \<lambda>cap. case cap of
      Some (Cap_untyped_cap c) \<Rightarrow> unat (cap_untyped_cap_CL.capBlockSize_CL c)
    | Some (Cap_endpoint_cap c) \<Rightarrow> epSizeBits
    | Some (Cap_notification_cap c) \<Rightarrow> ntfnSizeBits
    | Some (Cap_cnode_cap c) \<Rightarrow> unat (capCNodeRadix_CL c) + cteSizeBits
    | Some (Cap_thread_cap c) \<Rightarrow> tcbBlockSizeBits
    | Some (Cap_frame_cap c) \<Rightarrow> pageBitsForSize (framesize_to_H $ cap_frame_cap_CL.capFSize_CL c)
    | Some (Cap_page_table_cap c) \<Rightarrow> 12
    | Some (Cap_asid_pool_cap c) \<Rightarrow> 12
    | Some (Cap_zombie_cap c) \<Rightarrow>
        let type = cap_zombie_cap_CL.capZombieType_CL c in
        if isZombieTCB_C type
          then tcbBlockSizeBits
          else unat (type && mask wordRadix) + cteSizeBits
    | _ \<Rightarrow> 0"

lemma frame_cap_size [simp]:
  "cap_get_tag cap = scast cap_frame_cap
  \<Longrightarrow> cap_frame_cap_CL.capFSize_CL (cap_frame_cap_lift cap) && mask 2 =
     cap_frame_cap_CL.capFSize_CL (cap_frame_cap_lift cap)"
  apply (simp add: cap_frame_cap_lift_def)
  by (simp add: cap_lift_def cap_tag_defs)

lemma cap_get_tag_bound:
  "cap_get_tag x < 32"
  apply (simp add: cap_get_tag_def mask_def)
  by word_bitwise

lemma cap_get_tag_scast:
  "UCAST(64 \<rightarrow> 32 signed) (cap_get_tag cap) = tag \<longleftrightarrow> cap_get_tag cap = SCAST(32 signed \<rightarrow> 64) tag"
  apply (rule iffI; simp add: cap_get_tag_def)
  apply (drule sym; simp add: ucast_and_mask scast_eq_ucast msb_nth ucast_ucast_mask mask_twice)
  done

lemma cap_get_capSizeBits_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. c_valid_cap (cap_' s)\<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_get_capSizeBits(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = of_nat (get_capSizeBits_CL (cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capSizeBits_CL_def)
  apply (intro conjI impI;
         clarsimp simp: cap_lifts
                        cap_lift_asid_control_cap
                        cap_lift_irq_control_cap cap_lift_null_cap
                        Kernel_C.asidLowBits_def asid_low_bits_def
                        word_sle_def Let_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def
                        cap_lift_domain_cap cap_get_tag_scast
                        objBits_defs wordRadix_def
                        c_valid_cap_def cl_valid_cap_def
                 dest!: sym [where t = "ucast (cap_get_tag cap)" for cap])
  apply (clarsimp split: option.splits cap_CL.splits dest!: cap_lift_Some_CapD)
  done

lemma ccap_relation_get_capSizeBits_physical:
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap = PhysicalClass; capAligned hcap \<rbrakk>
   \<Longrightarrow> 2 ^ get_capSizeBits_CL (cap_lift ccap) = capUntypedSize hcap"
  apply (cases hcap;
         (match premises in "hcap = ArchObjectCap c" for c \<Rightarrow> \<open>cases c\<close>)?;
         (frule (1) ccap_rel_cap_get_tag_cases_generic)?;
         (frule (2) ccap_rel_cap_get_tag_cases_arch)?;
         (frule cap_lifts[THEN iffD1])?)
  apply (all \<open>clarsimp simp: get_capSizeBits_CL_def objBits_simps Let_def RISCV64_H.capUntypedSize_def
                             asid_low_bits_def pt_bits_def asidPoolBits_def table_size\<close>)
  (* Zombie, Page, Untyped, CNode caps remain. *)
  apply (all \<open>thin_tac \<open>hcap = _\<close>\<close>)
  apply (all \<open>rule arg_cong[where f="\<lambda>s. 2 ^ s"]\<close>)
  apply (all \<open>simp add: ccap_relation_def cap_lift_defs cap_lift_def cap_tag_defs cap_to_H_def\<close>)
  (* Now just Zombie caps *)
  apply (clarsimp simp: Let_def objBits_simps' wordRadix_def capAligned_def
                        word_bits_def word_less_nat_alt
                intro!: less_mask_eq
                 split: if_splits)
  done

lemma ccap_relation_get_capSizeBits_untyped:
  "\<lbrakk> ccap_relation (UntypedCap d word bits idx) ccap \<rbrakk> \<Longrightarrow>
   get_capSizeBits_CL (cap_lift ccap) = bits"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  by (clarsimp simp: get_capSizeBits_CL_def ccap_relation_def
                        map_option_case cap_to_H_def cap_lift_def cap_tag_defs)

definition
  get_capZombieBits_CL :: "cap_zombie_cap_CL \<Rightarrow> machine_word" where
  "get_capZombieBits_CL \<equiv> \<lambda>cap.
      let type = cap_zombie_cap_CL.capZombieType_CL cap in
      if isZombieTCB_C type then 4 else type && mask 6"


lemma get_capSizeBits_valid_shift:
  "\<lbrakk> ccap_relation hcap ccap; capAligned hcap \<rbrakk> \<Longrightarrow>
   get_capSizeBits_CL (cap_lift ccap) < 64"
  apply (cases hcap;
         (match premises in "hcap = ArchObjectCap c" for c \<Rightarrow> \<open>cases c\<close>)?;
         (frule (1) ccap_rel_cap_get_tag_cases_generic)?;
         (frule (2) ccap_rel_cap_get_tag_cases_arch)?;
         (frule cap_lifts[THEN iffD1])?)
  (* Deal with simple cases quickly. *)
  apply (all \<open>clarsimp simp: get_capSizeBits_CL_def objBits_simps' wordRadix_def Let_def
                      split: option.splits if_splits;
              thin_tac \<open>hcap = _\<close>\<close>)
  (* Deal with non-physical caps quickly. *)
  apply (all \<open>(match conclusion in "case_cap_CL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ < _" \<Rightarrow>
              \<open>clarsimp simp: cap_lift_def cap_tag_defs\<close>)?\<close>)
  (* Slow cases: Zombie, Page, Untyped and CNode caps. *)
  apply (all \<open>clarsimp simp: cap_lift_def cap_lift_defs cap_tag_defs
                             ccap_relation_def cap_to_H_def Let_def
                             capAligned_def objBits_simps' word_bits_def
                             unat_ucast_less_no_overflow_simp\<close>)
  (* Zombie arithmetic. *)
  apply (subst less_mask_eq[where n=6]; clarsimp elim!: less_trans)
  done

lemma get_capSizeBits_valid_shift_word:
  "\<lbrakk> ccap_relation hcap ccap; capAligned hcap \<rbrakk> \<Longrightarrow>
   of_nat (get_capSizeBits_CL (cap_lift ccap)) < (0x40::machine_word)"
  apply (subgoal_tac "of_nat (get_capSizeBits_CL (cap_lift ccap)) < (of_nat 64::machine_word)", simp)
  apply (rule of_nat_mono_maybe, simp+)
  apply (simp add: get_capSizeBits_valid_shift)
  done

lemma cap_zombie_cap_get_capZombieBits_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_zombie_cap \<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_zombie_cap_get_capZombieBits(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = get_capZombieBits_CL (cap_zombie_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capZombieBits_CL_def word_sle_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def Let_def)
  done

definition
  get_capZombiePtr_CL :: "cap_zombie_cap_CL \<Rightarrow> machine_word" where
  "get_capZombiePtr_CL \<equiv> \<lambda>cap.
      let radix = unat (get_capZombieBits_CL cap) in
      cap_zombie_cap_CL.capZombieID_CL cap && ~~ (mask (radix+1))"

lemma cap_zombie_cap_get_capZombiePtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. cap_get_tag \<acute>cap = scast cap_zombie_cap
                \<and> get_capZombieBits_CL (cap_zombie_cap_lift \<acute>cap) < 0x3F \<rbrace>
       \<acute>ret__unsigned_long :== PROC cap_zombie_cap_get_capZombiePtr(\<acute>cap)
       \<lbrace>\<acute>ret__unsigned_long = get_capZombiePtr_CL (cap_zombie_cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capZombiePtr_CL_def word_sle_def mask_def
                        isZombieTCB_C_def ZombieTCB_C_def Let_def)
  apply (intro conjI)
   apply (simp add: word_add_less_mono1[where k=1 and j="0x3F", simplified])
  apply (subst unat_plus_if_size)
  apply (clarsimp split: if_split)
  apply (clarsimp simp: get_capZombieBits_CL_def Let_def word_size
                 split: if_split if_split_asm)
  apply (subgoal_tac "unat (capZombieType_CL (cap_zombie_cap_lift cap) && mask 6)
                      < unat ((2::machine_word) ^ 6)")
   apply clarsimp
  apply (rule unat_mono)
  apply (rule and_mask_less_size)
  apply (clarsimp simp: word_size)
  done

definition
  get_capPtr_CL :: "cap_CL option \<Rightarrow> unit ptr" where
  "get_capPtr_CL \<equiv> \<lambda>cap. Ptr (case cap of
      Some (Cap_untyped_cap c) \<Rightarrow> cap_untyped_cap_CL.capPtr_CL c
    | Some (Cap_endpoint_cap c) \<Rightarrow> cap_endpoint_cap_CL.capEPPtr_CL c
    | Some (Cap_notification_cap c) \<Rightarrow> cap_notification_cap_CL.capNtfnPtr_CL c
    | Some (Cap_cnode_cap c) \<Rightarrow> cap_cnode_cap_CL.capCNodePtr_CL c
    | Some (Cap_thread_cap c) \<Rightarrow> (cap_thread_cap_CL.capTCBPtr_CL c && ~~ mask (objBits (undefined :: tcb)))
    | Some (Cap_frame_cap c) \<Rightarrow> cap_frame_cap_CL.capFBasePtr_CL c
    | Some (Cap_page_table_cap c) \<Rightarrow> cap_page_table_cap_CL.capPTBasePtr_CL c
    | Some (Cap_asid_pool_cap c) \<Rightarrow> cap_asid_pool_cap_CL.capASIDPool_CL c
    | Some (Cap_zombie_cap c) \<Rightarrow> get_capZombiePtr_CL c
    | _ \<Rightarrow> 0)"

lemma cap_get_capPtr_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. (cap_get_tag \<acute>cap = scast cap_zombie_cap
                   \<longrightarrow> get_capZombieBits_CL (cap_zombie_cap_lift \<acute>cap) < 0x3F)\<rbrace>
       \<acute>ret__ptr_to_void :== PROC cap_get_capPtr(\<acute>cap)
       \<lbrace>\<acute>ret__ptr_to_void = get_capPtr_CL (cap_lift \<^bsup>s\<^esup>cap)\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capPtr_CL_def)
  apply (intro impI conjI;
           clarsimp simp: cap_lifts pageBitsForSize_def
                          cap_lift_asid_control_cap word_sle_def
                          cap_lift_irq_control_cap cap_lift_null_cap
                          mask_def objBits_simps' cap_lift_domain_cap
                          ptr_add_assertion_positive cap_get_tag_scast
                    dest!: sym [where t = "ucast (cap_get_tag cap)" for cap]
                    split: vmpage_size.splits)+
  (* XXX: slow. there should be a rule for this *)
  by (case_tac "cap_lift cap", simp_all, case_tac "a",
      auto simp: cap_lift_def cap_lift_defs cap_tag_defs Let_def
          split: if_split_asm)

definition get_capIsPhysical_CL :: "cap_CL option \<Rightarrow> bool"
where
  "get_capIsPhysical_CL \<equiv> \<lambda>cap. (case cap of
  Some (Cap_untyped_cap c) \<Rightarrow> True
    | Some (Cap_endpoint_cap c) \<Rightarrow> True
    | Some (Cap_notification_cap c) \<Rightarrow> True
    | Some (Cap_cnode_cap c) \<Rightarrow> True
    | Some (Cap_thread_cap c) \<Rightarrow> True
    | Some (Cap_frame_cap c) \<Rightarrow> True
    | Some (Cap_page_table_cap c) \<Rightarrow> True
    | Some (Cap_asid_pool_cap c) \<Rightarrow> True
    | Some (Cap_zombie_cap c) \<Rightarrow> True
    | _ \<Rightarrow> False)"

lemma cap_get_capIsPhysical_spec:
  "\<forall>s. \<Gamma> \<turnstile> {s}
       Call cap_get_capIsPhysical_'proc
       \<lbrace>\<acute>ret__unsigned_long = from_bool (get_capIsPhysical_CL (cap_lift \<^bsup>s\<^esup>cap))\<rbrace>"
  apply vcg
  apply (clarsimp simp: get_capIsPhysical_CL_def)
  apply (intro impI conjI)
                    apply (clarsimp simp: cap_lifts pageBitsForSize_def
                                          cap_lift_asid_control_cap word_sle_def
                                          cap_lift_irq_control_cap cap_lift_null_cap
                                          mask_def objBits_simps cap_lift_domain_cap
                                          ptr_add_assertion_positive from_bool_def
                                          true_def false_def cap_get_tag_scast
                                   dest!: sym [where t = "ucast (cap_get_tag cap)" for cap]
                                   split: vmpage_size.splits)+
  sorry (* FIXME RISCV: almost certainly a relation/validity/spec bug which resulted False conclusion
  (* XXX: slow. there should be a rule for this *)
  by (case_tac "cap_lift cap", simp_all, case_tac a,
      auto simp: cap_lift_def cap_lift_defs cap_tag_defs Let_def
          split: if_split_asm)
  *)

lemma ccap_relation_get_capPtr_not_physical:
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap \<noteq> PhysicalClass \<rbrakk> \<Longrightarrow>
   get_capPtr_CL (cap_lift ccap) = Ptr 0"
  by (clarsimp simp: ccap_relation_def get_capPtr_CL_def cap_to_H_def Let_def
              split: option.split cap_CL.split_asm if_split_asm)

lemma ccap_relation_get_capIsPhysical:
  "ccap_relation hcap ccap \<Longrightarrow> isPhysicalCap hcap = get_capIsPhysical_CL (cap_lift ccap)"
  apply (case_tac hcap; clarsimp simp: cap_lifts cap_lift_domain_cap cap_lift_null_cap
                                       cap_lift_irq_control_cap cap_to_H_def
                                       get_capIsPhysical_CL_def
                       dest!: cap_get_tag_isCap_unfolded_H_cap)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap; clarsimp simp: cap_lifts cap_lift_asid_control_cap
                      dest!: cap_get_tag_isCap_unfolded_H_cap)
  done

lemma ctcb_ptr_to_tcb_ptr_mask':
  "is_aligned (ctcb_ptr_to_tcb_ptr (tcb_Ptr x)) (objBits (undefined :: tcb)) \<Longrightarrow>
     ctcb_ptr_to_tcb_ptr (tcb_Ptr x) = x && ~~ mask (objBits (undefined :: tcb))"
  apply (simp add: ctcb_ptr_to_tcb_ptr_def)
  apply (drule_tac d=ctcb_offset in is_aligned_add_helper)
   apply (simp add: objBits_simps' ctcb_offset_defs)
  apply simp
  done

lemmas ctcb_ptr_to_tcb_ptr_mask
    = ctcb_ptr_to_tcb_ptr_mask'[simplified objBits_simps, simplified]

lemma ccap_relation_get_capPtr_physical:
  "\<lbrakk> ccap_relation hcap ccap; capClass hcap = PhysicalClass; capAligned hcap \<rbrakk> \<Longrightarrow>
     get_capPtr_CL (cap_lift ccap)
        = Ptr (capUntypedPtr hcap)"
  apply (cases hcap;
         (match premises in "hcap = ArchObjectCap c" for c \<Rightarrow> \<open>cases c\<close>)?;
         (frule (1) ccap_rel_cap_get_tag_cases_generic)?;
         (frule (2) ccap_rel_cap_get_tag_cases_arch)?;
         (frule cap_lifts[THEN iffD1])?)
  apply (all \<open>clarsimp simp: get_capPtr_CL_def get_capZombiePtr_CL_def get_capZombieBits_CL_def
                             objBits_simps ccap_relation_def cap_to_H_def Let_def capAligned_def
                             ctcb_ptr_to_tcb_ptr_mask
                      split: if_splits;
         thin_tac \<open>hcap = _\<close>\<close>)
  apply (rule arg_cong[OF less_mask_eq])
  apply (clarsimp simp: cap_lift_def cap_lift_defs Let_def cap_tag_defs word_less_nat_alt
                        word_bits_conv)
  done

lemma ccap_relation_get_capPtr_untyped:
  "\<lbrakk> ccap_relation (UntypedCap d word bits idx) ccap \<rbrakk> \<Longrightarrow>
   get_capPtr_CL (cap_lift ccap) = Ptr word"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  by (clarsimp simp: get_capPtr_CL_def ccap_relation_def
                        map_option_case cap_to_H_def cap_lift_def cap_tag_defs)

lemma cap_get_tag_isArchCap_unfolded_H_cap:
  "ccap_relation (capability.ArchObjectCap a_cap) cap' \<Longrightarrow>
   (isArchCap_tag (cap_get_tag cap'))"
  apply (frule cap_get_tag_isCap(11), simp)
  done

lemmas ccap_rel_cap_get_tag_cases_generic' =
  ccap_rel_cap_get_tag_cases_generic
  cap_get_tag_isArchCap_unfolded_H_cap[OF back_subst[of "\<lambda>cap. ccap_relation cap cap'" for cap']]

lemma sameRegionAs_spec:
  notes cap_get_tag = ccap_rel_cap_get_tag_cases_generic'
  shows
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation capa \<acute>cap_a \<and> ccap_relation capb \<acute>cap_b \<and> capAligned capb\<rbrace>
  Call sameRegionAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (sameRegionAs capa capb) \<rbrace>"
  apply vcg
  apply clarsimp
  apply (simp add: sameRegionAs_def isArchCap_tag_def2 ccap_relation_c_valid_cap)
  apply (case_tac capa, simp_all add: cap_get_tag_isCap_unfolded_H_cap isCap_simps)
            \<comment> \<open>capa is a ThreadCap\<close>
             apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                          isCap_simps cap_tag_defs from_bool_def false_def)[1]
              apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(1))
              apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(1))
              apply (simp add: ccap_relation_def map_option_case)
              apply (simp add: cap_thread_cap_lift)
              apply (simp add: cap_to_H_def)
             apply (clarsimp simp: case_bool_If ctcb_ptr_to_tcb_ptr_def if_distrib
                              cong: if_cong)
             apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
             apply (clarsimp simp: isArchCap_tag_def2)
           \<comment> \<open>capa is a NullCap\<close>
            apply (simp add: cap_tag_defs from_bool_def false_def)
          \<comment> \<open>capa is an NotificationCap\<close>
           apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                        isCap_simps cap_tag_defs from_bool_def false_def)[1]
            apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(3))
            apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(3))
            apply (simp add: ccap_relation_def map_option_case)
            apply (simp add: cap_notification_cap_lift)
            apply (simp add: cap_to_H_def)
            apply (clarsimp split: if_split)
           apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
           apply (clarsimp simp: isArchCap_tag_def2)
          \<comment> \<open>capa is an IRQHandlerCap\<close>
          apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                      isCap_simps cap_tag_defs from_bool_def false_def)[1]
           apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(5))
           apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(5))
           apply (simp add: ccap_relation_def map_option_case)
           apply (simp add: cap_irq_handler_cap_lift)
           apply (simp add: cap_to_H_def)
           apply (clarsimp simp: up_ucast_inj_eq c_valid_cap_def ucast_eq_mask
                                 cl_valid_cap_def mask_twice
                          split: if_split bool.split
                  | intro impI conjI
                  | simp)
          apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
          apply (clarsimp simp: isArchCap_tag_def2)
         \<comment> \<open>capa is an EndpointCap\<close>
         apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                      isCap_simps cap_tag_defs from_bool_def false_def)[1]
          apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(4))
          apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(4))
          apply (simp add: ccap_relation_def map_option_case)
          apply (simp add: cap_endpoint_cap_lift)
          apply (simp add: cap_to_H_def)
          apply (clarsimp split: if_split)
         apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
         apply (clarsimp simp: isArchCap_tag_def2)
        \<comment> \<open>capa is a DomainCap\<close>
        apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                     isCap_simps cap_tag_defs from_bool_def false_def true_def)[1]
        apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
        apply (fastforce simp: isArchCap_tag_def2 split: if_split)
       \<comment> \<open>capa is a Zombie\<close>
       apply (simp add: cap_tag_defs from_bool_def false_def)
      \<comment> \<open>capa is an Arch object cap\<close>
      apply (frule_tac cap'=cap_a in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (clarsimp simp: isArchCap_tag_def2 cap_tag_defs linorder_not_less [THEN sym])
      apply (rule conjI, clarsimp, rule impI)+
      apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                   isCap_simps cap_tag_defs from_bool_def false_def)[1]
      \<comment> \<open>capb is an Arch object cap\<close>
      apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (fastforce simp: isArchCap_tag_def2 cap_tag_defs linorder_not_less [THEN sym])
     \<comment> \<open>capa is a ReplyCap\<close>
     apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                  isCap_simps cap_tag_defs from_bool_def false_def)[1]
      apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
      apply (clarsimp simp: isArchCap_tag_def2)
     apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(8))
     apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(8))
     apply (simp add: ccap_relation_def map_option_case)
     apply (simp add: cap_reply_cap_lift)
     apply (simp add: cap_to_H_def ctcb_ptr_to_tcb_ptr_def)
     apply (clarsimp split: if_split)
    \<comment> \<open>capa is an UntypedCap\<close>
    apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(9))
    apply (intro conjI)
     apply (rule impI, intro conjI)
        apply (rule impI, drule(1) cap_get_tag_to_H)+
        apply (clarsimp simp: capAligned_def word_bits_conv
                              objBits_simps' get_capZombieBits_CL_def
                              Let_def word_less_nat_alt
                              less_mask_eq true_def
                       split: if_split_asm)
       apply (subgoal_tac "capBlockSize_CL (cap_untyped_cap_lift cap_a) \<le> 0x3F")
        apply (simp add: word_le_make_less)
       apply (simp add: cap_untyped_cap_lift_def cap_lift_def
                        cap_tag_defs word_and_le1 mask_def)
      apply (clarsimp simp: get_capSizeBits_valid_shift_word)
     apply (clarsimp simp: from_bool_def Let_def split: if_split bool.splits)
     apply (subst unat_of_nat64,
              clarsimp simp: unat_of_nat64 word_bits_def
                      dest!: get_capSizeBits_valid_shift)+
     apply (clarsimp simp: ccap_relation_get_capPtr_physical
                           ccap_relation_get_capPtr_untyped
                           ccap_relation_get_capIsPhysical[symmetric]
                           ccap_relation_get_capSizeBits_physical
                           ccap_relation_get_capSizeBits_untyped)
     apply (intro conjI impI)
        apply ((clarsimp simp: ccap_relation_def map_option_case
                               cap_untyped_cap_lift cap_to_H_def
                               field_simps valid_cap'_def)+)[4]
    apply (rule impI, simp add: from_bool_0 ccap_relation_get_capIsPhysical[symmetric])
    apply (simp add: from_bool_def false_def)
   \<comment> \<open>capa is a CNodeCap\<close>
   apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                isCap_simps cap_tag_defs from_bool_def false_def)[1]
    apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
    apply (clarsimp simp: isArchCap_tag_def2)
   apply (frule_tac cap'=cap_a in cap_get_tag_isCap_unfolded_H_cap(10))
   apply (frule_tac cap'=cap_b in cap_get_tag_isCap_unfolded_H_cap(10))
   apply (simp add: ccap_relation_def map_option_case)
   apply (simp add: cap_cnode_cap_lift)
   apply (simp add: cap_to_H_def)
   apply (clarsimp split: if_split bool.split)
  \<comment> \<open>capa is an IRQControlCap\<close>
  apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
               isCap_simps cap_tag_defs from_bool_def false_def true_def)[1]
  apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
  apply (fastforce simp: isArchCap_tag_def2 split: if_split)
  done

lemma framesize_to_H_eq:
  "\<lbrakk> a \<le> 2; b \<le> 2 \<rbrakk> \<Longrightarrow>
   (framesize_to_H a = framesize_to_H b) = (a = b)"
  by (fastforce simp: framesize_to_H_def RISCV_4K_Page_def RISCV_Mega_Page_def RISCV_Giga_Page_def
                      word_le_make_less
               split: if_split
                dest: word_less_cases)

lemma capFSize_range:
  "\<And>cap. cap_get_tag cap = scast cap_frame_cap \<Longrightarrow> c_valid_cap cap \<Longrightarrow>
   capFSize_CL (cap_frame_cap_lift cap) \<le> 2"
  apply (simp add: cap_frame_cap_lift_def c_valid_cap_def cl_valid_cap_def)
  apply (clarsimp simp: cap_frame_cap_lift)
  apply (drule word_less_sub_1, simp)
  done

lemma ccap_relation_FrameCap_BasePtr:
  "ccap_relation (ArchObjectCap (FrameCap p r s d m)) ccap
    \<Longrightarrow> capFBasePtr_CL (cap_frame_cap_lift ccap) = p"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  by (clarsimp simp: ccap_relation_def cap_to_H_def cap_lift_def cap_lift_defs cap_tag_defs
                     Let_def)

lemma ccap_relation_FrameCap_IsDevice:
  "ccap_relation (ArchObjectCap (FrameCap p r s d m)) ccap
    \<Longrightarrow> capFIsDevice_CL (cap_frame_cap_lift ccap) = (if d then 1 else 0)"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: ccap_relation_def cap_to_H_def cap_lift_def cap_lift_defs cap_tag_defs
                        Let_def)
  apply (thin_tac _)+
  by (clarsimp simp: to_bool_def mask_def word_and_1 split: if_splits)

lemma ccap_relation_FrameCap_Size:
  "ccap_relation (ArchObjectCap (FrameCap p r s d m)) ccap
    \<Longrightarrow> capFSize_CL (cap_frame_cap_lift ccap) = framesize_from_H s"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (clarsimp simp: ccap_relation_def cap_to_H_def cap_lift_def cap_lift_defs cap_tag_defs
                        Let_def c_valid_cap_def cl_valid_cap_def)
  apply (thin_tac "p = _", thin_tac "r = _", thin_tac "d = _", thin_tac "m = _")
  apply (cases s; clarsimp simp: framesize_to_H_def framesize_from_H_def
                                 RISCV_4K_Page_def RISCV_Mega_Page_def RISCV_Giga_Page_def
                          split: if_splits cong: conj_cong)
  apply (word_bitwise, simp)
  done

lemma ccap_relation_FrameCap_MappedASID:
  "ccap_relation (ArchObjectCap (FrameCap p r s d (Some (a, b)))) ccap
    \<Longrightarrow> capFMappedASID_CL (cap_frame_cap_lift ccap) = a"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule cap_get_tag_PageCap_frame)
  apply (clarsimp split: if_split_asm)
  done

lemma ccap_relation_FrameCap_MappedAddress:
  "ccap_relation (ArchObjectCap (FrameCap p r s d (Some (a, b)))) ccap
    \<Longrightarrow> capFMappedAddress_CL (cap_frame_cap_lift ccap) = b"
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule cap_get_tag_PageCap_frame)
  apply (clarsimp split: if_split_asm)
  done

lemmas ccap_relation_FrameCap_fields =
  ccap_relation_FrameCap_BasePtr ccap_relation_FrameCap_IsDevice ccap_relation_FrameCap_Size

lemma case_bool_of_nat_eq:
  defines "cases_of c \<equiv> case c of True \<Rightarrow> of_nat 1 | False \<Rightarrow> of_nat 0"
  shows "(cases_of c = 0) = (\<not> c)"
        "(cases_of c = 1) = c"
        "(cases_of c = cases_of d) = (c = d)"
  by (cases c; simp add: cases_of_def; cases d; simp)+

lemma Arch_sameObjectAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation (ArchObjectCap capa) \<acute>cap_a \<and>
                     ccap_relation (ArchObjectCap capb) \<acute>cap_b \<and>
                     capAligned (ArchObjectCap capa) \<and>
                     capAligned (ArchObjectCap capb) \<rbrace>
  Call Arch_sameObjectAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (Arch.sameObjectAs capa capb) \<rbrace>"
  proof -
    note cap_get_tag = ccap_rel_cap_get_tag_cases_arch'
    note case_bool_of_nat_eq[simp]
    have [simp]: "(\<forall>d. d) = False" "(\<forall>d. \<not>d) = False" by auto
    show ?thesis
      apply vcg
      apply (clarsimp simp: RISCV64_H.sameObjectAs_def)
      subgoal for capa capb cap_b cap_a
      apply (cases capa)
      apply (all \<open>frule (1) cap_get_tag[where cap'=cap_a]\<close>)
      apply (all \<open>(frule cap_lifts[where c=cap_a, THEN iffD1])?\<close>)
      apply (all \<open>clarsimp simp: cap_tag_defs isCap_simps from_bool_def true_def false_def if_0_1_eq
                          split: if_splits\<close>)
      apply (all \<open>fastforce?\<close>)
      (* frames remain. *)
      apply (all \<open>cases capb\<close>)
      apply (all \<open>frule (1) cap_get_tag[where cap'=cap_b]\<close>)
      apply (all \<open>(frule cap_lifts[where c=cap_b, THEN iffD1])?\<close>)
      apply (all \<open>clarsimp simp: cap_tag_defs isCap_simps from_bool_def true_def false_def if_0_1_eq
                                 ccap_relation_FrameCap_fields framesize_from_H_eq capAligned_def
                          split: if_splits\<close>)
      apply (all \<open>(fastforce simp: RISCV64_H.sameRegionAs_def isCap_simps)?\<close>)
      (* FIXME RISCV: if aligned to n bits, then can add mask n without overflow, should be OK *)
      sorry
      done
  qed

lemma sameObjectAs_spec:
  "\<forall>capa capb. \<Gamma> \<turnstile> \<lbrace>ccap_relation capa \<acute>cap_a \<and>
                     ccap_relation capb \<acute>cap_b \<and>
                     capAligned capa \<and> capAligned capb \<and> (\<exists>s. s \<turnstile>' capa)\<rbrace>
  Call sameObjectAs_'proc
  \<lbrace> \<acute>ret__unsigned_long = from_bool (sameObjectAs capa capb) \<rbrace>"
  apply vcg
  apply (clarsimp simp: sameObjectAs_def isArchCap_tag_def2)
  apply (case_tac capa, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                      isCap_simps cap_tag_defs
                                      from_bool_def false_def)
            apply fastforce+
     \<comment> \<open>capa is an arch cap\<close>
     apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
     apply (simp add: isArchCap_tag_def2)
     apply (rule conjI, rule impI, clarsimp, rule impI)+
     apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                         isCap_simps cap_tag_defs)[1]
                apply ((fastforce)+)[7]
         \<comment> \<open>capb is an arch cap\<close>
         apply (frule_tac cap'=cap_b in cap_get_tag_isArchCap_unfolded_H_cap)
         apply (fastforce simp: isArchCap_tag_def2 linorder_not_less [symmetric])+
  \<comment> \<open>capa is an irq handler cap\<close>
  apply (case_tac capb, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                                      isCap_simps cap_tag_defs)
           apply fastforce+
      \<comment> \<open>capb is an arch cap\<close>
      apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
      apply (fastforce simp: isArchCap_tag_def2)+
  done

lemma sameRegionAs_EndpointCap:
  shows "\<lbrakk>ccap_relation capa capc;
          RetypeDecls_H.sameRegionAs (capability.EndpointCap p b cs cr cg cgr) capa\<rbrakk>
         \<Longrightarrow> cap_get_tag capc = scast cap_endpoint_cap"
  apply (simp add: sameRegionAs_def Let_def)
  apply (case_tac capa;
         simp add: isUntypedCap_def isEndpointCap_def isNotificationCap_def
             isCNodeCap_def isThreadCap_def isReplyCap_def isIRQControlCap_def
             isIRQHandlerCap_def isArchObjectCap_def)
  apply (clarsimp simp: ccap_relation_def map_option_case)
  apply (case_tac "cap_lift capc"; simp)
  apply (simp add: cap_to_H_def)
  apply (case_tac a; simp)
   apply (simp add:cap_endpoint_cap_lift cap_endpoint_cap_lift_def)
  apply (rename_tac zombie_cap)
  apply (case_tac "isZombieTCB_C (capZombieType_CL zombie_cap)"; simp add: Let_def)
  done

lemma sameRegionAs_NotificationCap:
  shows "\<lbrakk>ccap_relation capa capc;
          RetypeDecls_H.sameRegionAs
            (capability.NotificationCap x y z  u ) capa\<rbrakk>
         \<Longrightarrow> cap_get_tag capc = scast cap_notification_cap"
  apply (simp add: sameRegionAs_def  Let_def)
  apply (case_tac capa;
         simp add: isUntypedCap_def isEndpointCap_def isNotificationCap_def
             isCNodeCap_def isThreadCap_def isReplyCap_def isIRQControlCap_def
             isIRQHandlerCap_def isArchObjectCap_def)
  apply (clarsimp simp: ccap_relation_def map_option_case)
  apply (case_tac "cap_lift capc"; simp)
  apply (simp add: cap_to_H_def)
  apply (case_tac a; simp)
   apply (simp add: cap_notification_cap_lift cap_notification_cap_lift_def)
  apply (rename_tac zombie_cap)
  apply (case_tac "isZombieTCB_C (capZombieType_CL zombie_cap)"; simp add: Let_def)
  done

lemma isMDBParentOf_spec:
  notes option.case_cong_weak [cong]
  shows "\<forall>ctea cte_a cteb cte_b.
   \<Gamma> \<turnstile> {s. cslift s (cte_a_' s) = Some cte_a \<and>
            ccte_relation ctea cte_a \<and>
            cslift s (cte_b_' s) = Some cte_b \<and>
            ccte_relation cteb cte_b \<and>
            capAligned (cteCap cteb) \<and>
            (\<exists>s. s \<turnstile>' (cteCap ctea)) }
   Call isMDBParentOf_'proc
   \<lbrace> \<acute>ret__unsigned_long = from_bool (isMDBParentOf ctea cteb) \<rbrace>"
  apply (intro allI, rule conseqPre)
   apply vcg
  apply (clarsimp simp: isMDBParentOf_def)
  apply (frule_tac cte=ctea in ccte_relation_ccap_relation)
  apply (frule_tac cte=cteb in ccte_relation_ccap_relation)

  apply (rule conjI, clarsimp simp: typ_heap_simps dest!: lift_t_g)
  apply (intro conjI impI)
     apply (simp add: ccte_relation_def map_option_case)
     apply (simp add: cte_lift_def)
     apply (clarsimp simp: cte_to_H_def mdb_node_to_H_def split: option.split_asm)
     apply (clarsimp simp: Let_def false_def from_bool_def to_bool_def
                    split: if_split bool.splits)
     apply ((clarsimp simp: typ_heap_simps dest!: lift_t_g)+)[3]
  apply (rule_tac x="cteCap ctea" in exI, rule conjI)
   apply (clarsimp simp: ccte_relation_ccap_relation typ_heap_simps
                  dest!: lift_t_g)
  apply (rule_tac x="cteCap cteb" in exI, rule conjI)
   apply (clarsimp simp: ccte_relation_ccap_relation typ_heap_simps
                  dest!: lift_t_g)
  apply (clarsimp simp: ccte_relation_def map_option_case)
  apply (simp add: cte_lift_def)
  apply (clarsimp simp: cte_to_H_def mdb_node_to_H_def
                 split: option.split_asm)

  apply (rule conjI)
   \<comment> \<open>sameRegionAs = 0\<close>
   apply (rule impI)
   apply (clarsimp simp: from_bool_def false_def
                  split: if_split bool.splits)

  \<comment> \<open>sameRegionAs \<noteq> 0\<close>
  apply (clarsimp simp: from_bool_def false_def)
  apply (clarsimp cong:bool.case_cong if_cong simp: typ_heap_simps)

  apply (rule conjI)
    \<comment> \<open>cap_get_tag of cte_a is an endpoint\<close>
   apply clarsimp
   apply (frule cap_get_tag_EndpointCap)
   apply simp
   apply (clarsimp simp: to_bool_def isNotificationCap_def isEndpointCap_def true_def) \<comment> \<open>badge of A is not 0 now\<close>


   apply (subgoal_tac "cap_get_tag (cte_C.cap_C cte_b) = scast cap_endpoint_cap") \<comment> \<open>needed also after\<close>
    prefer 2
    apply (rule sameRegionAs_EndpointCap, assumption+)

   apply (clarsimp simp: if_1_0_0 typ_heap_simps'   Let_def case_bool_If)
   apply (frule_tac cap="(cap_to_H x2c)" in cap_get_tag_EndpointCap)
   apply (clarsimp split: if_split_asm simp: if_distrib [where f=scast])

  apply (clarsimp, rule conjI)
  \<comment> \<open>cap_get_tag of cte_a is an notification\<close>
   apply clarsimp
   apply (frule cap_get_tag_NotificationCap)
   apply simp
   apply (clarsimp simp: to_bool_def isNotificationCap_def isEndpointCap_def true_def) \<comment> \<open>badge of A is not 0 now\<close>


   apply (subgoal_tac "cap_get_tag (cte_C.cap_C cte_b) = scast cap_notification_cap") \<comment> \<open>needed also after\<close>
    prefer 2
    apply (rule sameRegionAs_NotificationCap, assumption+)

   apply (rule conjI, simp)
   apply clarsimp
   apply (simp add: Let_def case_bool_If)
   apply (frule_tac cap="(cap_to_H x2c)" in cap_get_tag_NotificationCap)
   apply clarsimp

  \<comment> \<open>main goal\<close>
  apply clarsimp
  apply (simp add: to_bool_def)
  apply (subgoal_tac "(\<not> (isEndpointCap (cap_to_H x2b))) \<and> ( \<not> (isNotificationCap (cap_to_H x2b)))")
   apply (clarsimp simp: true_def)
  apply (clarsimp simp: cap_get_tag_isCap [symmetric])
  done

lemma updateCapData_spec:
  "\<forall>cap. \<Gamma> \<turnstile> \<lbrace> ccap_relation cap \<acute>cap \<and> preserve = to_bool (\<acute>preserve) \<and> newData = \<acute>newData\<rbrace>
  Call updateCapData_'proc
  \<lbrace>  ccap_relation (updateCapData preserve newData cap) \<acute>ret__struct_cap_C \<rbrace>"
  apply (rule allI, rule conseqPre)
  apply vcg
  apply (clarsimp simp: if_1_0_0)

  apply (simp add: updateCapData_def)

  apply (case_tac cap, simp_all add: cap_get_tag_isCap_unfolded_H_cap
                        isCap_simps from_bool_def isArchCap_tag_def2 cap_tag_defs Let_def)
  \<comment> \<open>NotificationCap\<close>
     apply clarsimp
     apply (frule cap_get_tag_isCap_unfolded_H_cap(3))
     apply (frule (1) iffD1[OF cap_get_tag_NotificationCap])
     apply clarsimp

     apply (intro conjI impI)
     \<comment> \<open>preserve is zero and capNtfnBadge_CL \<dots> = 0\<close>
       apply clarsimp
       apply (clarsimp simp:cap_notification_cap_lift_def cap_lift_def cap_tag_defs)
       apply (simp add: ccap_relation_def cap_lift_def cap_tag_defs cap_to_H_def)
     \<comment> \<open>preserve is zero and capNtfnBadge_CL \<dots> \<noteq> 0\<close>
      apply clarsimp
      apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)
     \<comment> \<open>preserve is not zero\<close>
     apply clarsimp
     apply (simp add: to_bool_def)
     apply (case_tac "preserve_' x = 0 \<and> capNtfnBadge_CL (cap_notification_cap_lift (cap_' x))= 0",
            clarsimp)
     apply (simp add: if_not_P)
     apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)

  \<comment> \<open>EndpointCap\<close>
    apply clarsimp
    apply (frule cap_get_tag_isCap_unfolded_H_cap(4))
    apply (frule (1) iffD1[OF cap_get_tag_EndpointCap])
    apply clarsimp

    apply (intro impI conjI)
    \<comment> \<open>preserve is zero and capNtfnBadge_CL \<dots> = 0\<close>
      apply clarsimp
      apply (clarsimp simp:cap_endpoint_cap_lift_def cap_lift_def cap_tag_defs)
      apply (simp add: ccap_relation_def cap_lift_def cap_tag_defs cap_to_H_def)
    \<comment> \<open>preserve is zero and capNtfnBadge_CL \<dots> \<noteq> 0\<close>
     apply clarsimp
     apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)
    \<comment> \<open>preserve is not zero\<close>
    apply clarsimp
    apply (simp add: to_bool_def)
    apply (case_tac "preserve_' x = 0 \<and> capEPBadge_CL (cap_endpoint_cap_lift (cap_' x))= 0", clarsimp)
    apply (simp add: if_not_P)
    apply (simp add: ccap_relation_NullCap_iff cap_tag_defs)

  \<comment> \<open>ArchObjectCap\<close>
   apply clarsimp
   apply (frule cap_get_tag_isArchCap_unfolded_H_cap)
   apply (simp add: isArchCap_tag_def2)
   apply (simp add: RISCV64_H.updateCapData_def)

  \<comment> \<open>CNodeCap\<close>
  apply (clarsimp simp: cteRightsBits_def cteGuardBits_def)
  apply (frule cap_get_tag_isCap_unfolded_H_cap(10))
  apply (frule (1) iffD1[OF cap_get_tag_CNodeCap])
  apply clarsimp

  apply (thin_tac "ccap_relation x y" for x y)
  apply (thin_tac "ret__unsigned_long_' t = v" for t v)+

  apply (simp add: seL4_CNode_CapData_lift_def fupdate_def word_size word_less_nat_alt mask_def
             cong: if_cong)
  apply (simp only: unat_word_ariths(1))
  apply (rule ssubst [OF nat_mod_eq' [where n = "2 ^ len_of TYPE(64)"]])
   \<comment> \<open>unat (\<dots> && 0x3F) +  unat (\<dots> mod 0x40) < 2 ^ len_of TYPE(64)\<close>
   apply (rule order_le_less_trans, rule add_le_mono)
     apply (rule word_le_nat_alt[THEN iffD1])
     apply (rule word_and_le1)
    apply (simp add: cap_cnode_cap_lift_def cap_lift_cnode_cap)
    apply (rule word_le_nat_alt[THEN iffD1])
    apply (rule word_and_le1)
   apply (simp add: mask_def)

  apply (simp add: word_sle_def)
  apply (rule conjI, clarsimp simp:  ccap_relation_NullCap_iff cap_tag_defs)
  apply clarsimp
  apply (rule conjI)
   apply (rule unat_less_power[where sz=6, simplified], simp add: word_bits_def)
   apply (rule and_mask_less'[where n=6, unfolded mask_def, simplified], simp)

  apply clarsimp
  apply (simp add: ccap_relation_def c_valid_cap_def cl_valid_cap_def
                   cap_lift_cnode_cap cap_tag_defs cap_to_H_simps
                   cap_cnode_cap_lift_def)
  apply (simp add: word_bw_assocs word_bw_comms word_bw_lcs)
  done

abbreviation
  "deriveCap_xf \<equiv> liftxf errstate deriveCap_ret_C.status_C deriveCap_ret_C.cap_C ret__struct_deriveCap_ret_C_'"

(* FIXME RISCV: override original, r is a poor variable name here and diverges from X64 *)
lemmas ctes_of_valid'[elim] = ctes_of_valid_cap''[where r=cte for cte]

lemma ensureNoChildren_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id undefined ret__unsigned_long_')
   (\<lambda>s. valid_objs' s \<and> valid_mdb' s) (UNIV \<inter> \<lbrace>slot = ptr_val (\<acute>slot)\<rbrace>) []
   (ensureNoChildren slot) (Call ensureNoChildren_'proc)"
   apply (cinit lift: slot_')
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_getCTE)
   apply (rule ccorres_move_c_guard_cte)

   apply (rule_tac P= "\<lambda> s. valid_objs' s \<and> valid_mdb' s \<and> ctes_of s (ptr_val slota) = Some cte"
               and P' =UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp

   apply (frule (1) rf_sr_ctes_of_clift, clarsimp)
   apply (simp add: typ_heap_simps)

   apply (clarsimp simp: whenE_def throwError_def return_def nullPointer_def liftE_bindE)

   apply (clarsimp simp: returnOk_def return_def) \<comment> \<open>solve the case where mdbNext is zero\<close>

   \<comment> \<open>main goal\<close>
   apply (simp add: ccte_relation_def)
   apply (frule_tac cte="cte_to_H y" in valid_mdb_ctes_of_next, simp+)
   apply (clarsimp simp: cte_wp_at_ctes_of)
   apply (frule_tac cte=cte in rf_sr_ctes_of_clift, assumption, clarsimp)
   apply (rule conjI)
    apply (frule_tac cte="(cte_to_H ya)" in ctes_of_valid', assumption, simp)
    apply (rule valid_capAligned, assumption)
   apply (rule conjI)
    apply (frule_tac cte="(cte_to_H y)" in ctes_of_valid', assumption, simp)
    apply blast

   apply clarsimp
   apply (rule conjI)
   \<comment> \<open>isMDBParentOf is not zero\<close>
    apply clarsimp
    apply (simp add: from_bool_def)
    apply (case_tac "isMDBParentOf (cte_to_H y) (cte_to_H ya)", simp_all)[1]

    apply (simp add: bind_def)
    apply (simp add: split_paired_Bex)
    apply (clarsimp simp: in_getCTE_cte_wp_at')
    apply (simp add: cte_wp_at_ctes_of)
    apply (simp add: syscall_error_rel_def EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
    apply (simp add: syscall_error_to_H_cases(9))
   \<comment> \<open>isMDBParentOf is zero\<close>
   apply clarsimp
   apply (simp add: from_bool_def)
   apply (case_tac "isMDBParentOf (cte_to_H y) (cte_to_H ya)", simp_all)[1]
   apply (simp add: bind_def)
   apply (simp add: split_paired_Bex)
   apply (clarsimp simp: in_getCTE_cte_wp_at')
   apply (simp add: cte_wp_at_ctes_of)
   apply (simp add: returnOk_def return_def)

  \<comment> \<open>last goal\<close>
  apply clarsimp
  apply (simp add: cte_wp_at_ctes_of)
  done

lemma Arch_deriveCap_ccorres:
  "ccorres (syscall_error_rel \<currency> ccap_relation) deriveCap_xf
  \<top> (UNIV \<inter> {s. ccap_relation (ArchObjectCap cap) (cap_' s)}) []
  (Arch.deriveCap slot cap) (Call Arch_deriveCap_'proc)"
  apply (cinit lift: cap_')
   apply csymbr
   apply (unfold RISCV64_H.deriveCap_def Let_def)
   apply (fold case_bool_If)
   (* FIXME RISCV: this proof needs more detailed examination; check which bits correspond to which
                   arch objects on X64, since we don't have all of them on RISCV64
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: returnOk_def return_def)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def
                          cap_page_table_cap_lift_def)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: throwError_def return_def
                          errstate_def syscall_error_rel_def
                          syscall_error_to_H_cases
                          exception_defs)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def to_bool_def
                          cap_page_table_cap_lift_def
                   split: if_split_asm)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: returnOk_def return_def)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply clarsimp
    apply (rule context_conjI)
     apply (simp add: cap_get_tag_isCap_ArchObject)
    apply (clarsimp simp: throwError_def return_def
                          errstate_def syscall_error_rel_def
                          syscall_error_to_H_cases
                          exception_defs)
    subgoal by (simp add: ccap_relation_def cap_lift_def Let_def
                          cap_tag_defs cap_to_H_def to_bool_def
                          cap_page_directory_cap_lift_def
                   split: if_split_asm)
   \<comment> \<open>FrameCap\<close>
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap_ArchObject
                          ccorres_cond_iffs)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: cap_get_tag_isCap_unfolded_H_cap isCap_simps)
    apply (rule context_conjI)
     apply (simp add: cap_tag_defs)
    apply (clarsimp simp: returnOk_def return_def isCap_simps)
    subgoal apply (frule cap_get_tag_isCap_unfolded_H_cap)
      by (clarsimp simp: cap_frame_cap_lift[simplified cap_tag_defs, simplified] cap_tag_defs
                         ccap_relation_def cap_to_H_def asidInvalid_def maptype_to_H_def
                         vm_page_map_type_defs c_valid_cap_def cl_valid_cap_def
                  split: if_splits)
   apply (simp add: cap_get_tag_isCap_ArchObject
                    ccorres_cond_iffs)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: returnOk_def return_def subset_iff
                  split: bool.split)
   apply (cases cap, simp_all add: isCap_simps ccap_relation_NullCap_iff)[1]
  apply clarsimp
  done *)
  sorry

lemma isArchCap_T_isArchObjectCap:
  "isArchCap \<top> = isArchObjectCap"
  by (rule ext, auto simp: isCap_simps)

lemma deriveCap_ccorres':
  "ccorres (syscall_error_rel \<currency> ccap_relation) deriveCap_xf
  (valid_objs' and valid_mdb') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. slot_' s = Ptr slot}) []
  (deriveCap slot cap) (Call deriveCap_'proc)"
  apply (cinit lift: cap_' slot_')
   apply csymbr
   apply (fold case_bool_If)
   apply wpc
    apply (clarsimp simp: cap_get_tag_isCap isCap_simps from_bool_def)
    apply csymbr
    apply (clarsimp simp: cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws [where P=\<top> and P' = UNIV])
    apply (simp add: returnOk_def return_def ccap_relation_NullCap_iff)
    apply (rule allI, rule conseqPre)
     apply vcg
    apply clarsimp
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: returnOk_def return_def
                          ccap_relation_NullCap_iff)
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_rhs_assoc)+
    apply ctac_print_xf
    apply (rule ccorres_split_nothrow_call_novcgE
                   [where xf'="ret__unsigned_long_'"])
           apply (rule ensureNoChildren_ccorres)
          apply simp+
       apply ceqv
      apply simp
      apply (rule_tac P'="\<lbrace>\<acute>ret__unsigned_long = scast EXCEPTION_NONE\<rbrace>"
                 in ccorres_from_vcg_throws[where P=\<top>])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def returnOk_def)
     apply simp
     apply (rule_tac P'="{s. ret__unsigned_long_' s = rv' \<and> errstate s = err'}"
                in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: throwError_def return_def
                           errstate_def)
    apply wp
   apply wpc
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap from_bool_def)
    apply csymbr
    apply (clarsimp simp: isCap_simps cap_get_tag_isCap)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: returnOk_def return_def
                          ccap_relation_NullCap_iff)
   apply wpc
    apply (rule ccorres_split_throws[rotated])
     apply (clarsimp simp: cap_get_tag_isCap
                           liftME_def Let_def isArchCap_T_isArchObjectCap)
     apply vcg
    apply (clarsimp simp: cap_get_tag_isCap
                          liftME_def Let_def isArchCap_T_isArchObjectCap
                          ccorres_cond_univ_iff from_bool_def)
    apply (rule ccorres_add_returnOk)
    apply (rule ccorres_split_nothrow_call_novcgE
                    [where xf'=ret__struct_deriveCap_ret_C_'])
           apply (rule Arch_deriveCap_ccorres)
          apply simp+
       apply (rule ceqv_refl)
      apply (rule_tac P'="\<lbrace>\<acute>ret__struct_deriveCap_ret_C
                              = rv'\<rbrace>"
                 in ccorres_from_vcg_throws[where P=\<top>])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def returnOk_def)
     apply (rule_tac P'="{s. (ret__struct_deriveCap_ret_C_' s)
                               = rv' \<and> errstate s = err'}"
                in ccorres_from_vcg_throws[where P=\<top>])
     apply (rule allI, rule conseqPre, vcg)
     apply (clarsimp simp: return_def throwError_def)
    apply wp
   apply (simp add: cap_get_tag_isCap isArchCap_T_isArchObjectCap from_bool_def)
   apply csymbr
   apply (simp add: cap_get_tag_isCap)
   apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
   apply (rule allI, rule conseqPre, vcg)
   apply (clarsimp simp: return_def returnOk_def)
  apply (clarsimp simp: errstate_def isCap_simps
                        Collect_const_mem from_bool_0
                        cap_get_tag_isArchCap_unfolded_H_cap)
  done


lemma deriveCap_ccorres:
  "ccorres (syscall_error_rel \<currency> ccap_relation) deriveCap_xf
  (invs') (UNIV \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. slot_' s = Ptr slot}) []
  (deriveCap slot cap) (Call deriveCap_'proc)"
  apply (rule ccorres_guard_imp2, rule deriveCap_ccorres')
  apply fastforce
  done

lemma ensureEmptySlot_ccorres:
  "ccorres (syscall_error_rel \<currency> dc) (liftxf errstate id undefined ret__unsigned_long_')
   \<top>  (UNIV \<inter> \<lbrace>slot = ptr_val (\<acute>slot)\<rbrace>) []
   (ensureEmptySlot slot) (Call ensureEmptySlot_'proc)"
  apply (cinit lift: slot_')
   apply (rule ccorres_liftE_Seq)
   apply (rule ccorres_getCTE)
   apply (rule ccorres_move_c_guard_cte)
   apply (rule_tac P= "\<lambda> s. ctes_of s (ptr_val slota) = Some cte"
               and P' =UNIV in ccorres_from_vcg_throws)
   apply (rule allI, rule conseqPre, vcg)
   apply clarsimp

   apply (frule (1) rf_sr_ctes_of_clift, clarsimp)
   apply (simp add: typ_heap_simps)

   apply (rule conjI)
    apply (clarsimp simp: unlessE_def throwError_def return_def)
    apply (subgoal_tac "cap_to_H (cap_CL y) \<noteq> capability.NullCap")
     apply simp
     apply (simp add: syscall_error_rel_def EXCEPTION_NONE_def EXCEPTION_SYSCALL_ERROR_def)
     apply (rule syscall_error_to_H_cases(8))
     apply simp
    apply (subst cap_get_tag_NullCap [symmetric])
     prefer 2 apply assumption
    apply (simp add: ccap_relation_def c_valid_cte_def)

   apply (clarsimp simp: unlessE_def throwError_def return_def)
   apply (subgoal_tac "cap_to_H (cap_CL y) = capability.NullCap")
    apply simp
    apply (simp add: returnOk_def return_def)
   apply (subst cap_get_tag_NullCap [symmetric])
    prefer 2 apply assumption
   apply (simp add: ccap_relation_def c_valid_cte_def)

  apply clarsimp
  apply (simp add: cte_wp_at_ctes_of)
done

lemma updateMDB_set_mdbPrev:
 "ccorres dc xfdc
          (\<lambda>s. is_aligned slota cteSizeBits)
          {s. slotc = slota } hs
          (updateMDB ptr (mdbPrev_update (\<lambda>_. slota)))
          (IF ptr \<noteq> 0
           THEN
             Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr ptr:: cte_C ptr)\<rbrace>
                   (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr ptr:: cte_C ptr\<rightarrow>[''cteMDBNode_C'']),
                                     v64_' := slotc |))
                    mdb_node_ptr_set_mdbPrev_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
           FI)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbPrev)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply (simp)
  done

lemma updateMDB_set_mdbNext:
 "ccorres dc xfdc
          (\<lambda>s. is_aligned slota cteSizeBits \<and> canonical_address slota)
          {s. slotc = slota} hs
          (updateMDB ptr (mdbNext_update (\<lambda>_. slota)))
          (IF ptr \<noteq> 0
           THEN
             Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr ptr:: cte_C ptr)\<rbrace>
                   (call (\<lambda>ta. ta(| mdb_node_ptr_' := Ptr &(Ptr ptr:: cte_C ptr\<rightarrow>[''cteMDBNode_C'']),
                                     v64_' := slotc |))
                    mdb_node_ptr_set_mdbNext_'proc (\<lambda>s t. s\<lparr> globals := globals t \<rparr>) (\<lambda>ta s'. Basic (\<lambda>a. a)))
           FI)"
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_Cond_rhs)
    apply (rule ccorres_updateMDB_cte_at)
    apply (ctac add: ccorres_updateMDB_set_mdbNext)
   apply (ctac ccorres: ccorres_updateMDB_skip)
  apply simp
  done

end
end
