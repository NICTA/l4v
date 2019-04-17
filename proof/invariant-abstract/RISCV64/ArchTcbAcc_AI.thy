(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTcbAcc_AI
imports "../TcbAcc_AI"
begin

context Arch begin global_naming RISCV64

named_theorems TcbAcc_AI_assms

lemmas cap_master_cap_simps =
  cap_master_cap_def[simplified cap_master_arch_cap_def, split_simps cap.split arch_cap.split]

lemma cap_master_cap_arch_eqDs:
  "cap_master_cap cap = ArchObjectCap (FrameCap ref rghts sz dev mapdata)
     \<Longrightarrow> rghts = UNIV \<and> mapdata = None
          \<and> (\<exists>rghts mapdata. cap = cap.ArchObjectCap (FrameCap ref rghts sz dev mapdata))"
  "cap_master_cap cap = ArchObjectCap ASIDControlCap
     \<Longrightarrow> cap = ArchObjectCap ASIDControlCap"
  "cap_master_cap cap = ArchObjectCap (ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ArchObjectCap (ASIDPoolCap pool asid))"
  "cap_master_cap cap = ArchObjectCap (PageTableCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageTableCap ptr data))"
  by (clarsimp simp: cap_master_cap_def
              split: cap.split_asm arch_cap.split_asm)+

lemmas cap_master_cap_eqDs =
  cap_master_cap_eqDs1 cap_master_cap_arch_eqDs
  cap_master_cap_eqDs1 [OF sym] cap_master_cap_arch_eqDs[OF sym]


lemma vm_sets_diff[simp]:
  "vm_read_only \<noteq> vm_read_write"
  by (simp add: vm_read_write_def vm_read_only_def)


lemmas vm_sets_diff2[simp] = not_sym[OF vm_sets_diff]

lemma cap_master_cap_tcb_cap_valid_arch:
  "\<lbrakk> cap_master_cap c = cap_master_cap c'; is_arch_cap c' ;
     is_valid_vtable_root c \<Longrightarrow> is_valid_vtable_root c' ; tcb_cap_valid c p s \<rbrakk> \<Longrightarrow>
   tcb_cap_valid c' p s"
  (* slow: 5 to 10s *)
  by (auto simp: cap_master_cap_def tcb_cap_valid_def tcb_cap_cases_def
                 valid_ipc_buffer_cap_def  is_cap_simps
                 is_nondevice_page_cap_simps
           elim: pred_tcb_weakenE
          split: option.splits cap.splits arch_cap.splits
                 Structures_A.thread_state.splits)

lemma storeWord_invs[wp, TcbAcc_AI_assms]:
  "\<lbrace>in_user_frame p and invs\<rbrace> do_machine_op (storeWord p w) \<lbrace>\<lambda>rv. invs\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l sz. \<lbrakk> l<2^pte_bits; p && mask pte_bits = 0 \<rbrakk> \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l::machine_word and sz
    assume al: "p && mask pte_bits = 0"
    assume less: "l<2^pte_bits"
    have le: "pte_bits \<le> pageBitsForSize sz" by (case_tac sz, simp_all add: bit_simps)
    show "?thesis l sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=pte_bits, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs)
    apply (clarsimp simp: storeWord_def invs_def valid_state_def)
    sorry (* FIXME RISCV
    apply (fastforce simp: valid_machine_state_def in_user_frame_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
             split: if_split_asm)
    done *)
qed

lemma valid_ipc_buffer_cap_0[simp, TcbAcc_AI_assms]:
  "valid_ipc_buffer_cap cap a \<Longrightarrow> valid_ipc_buffer_cap cap 0"
  by (auto simp add: valid_ipc_buffer_cap_def case_bool_If
    split: cap.split arch_cap.split)

lemma thread_set_hyp_refs_trivial [TcbAcc_AI_assms]:
  assumes x: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule all_ext;
         clarsimp simp: state_hyp_refs_of_def hyp_refs_of_def tcb_hyp_refs_def get_tcb_def x y[simplified tcb_arch_ref_def])
  done

lemma mab_pb [simp]:
  "msg_align_bits \<le> pageBits"
  unfolding msg_align_bits pageBits_def by simp

lemma mab_wb [simp]:
  "msg_align_bits < word_bits"
  unfolding msg_align_bits word_bits_conv by simp


lemma get_cap_valid_ipc [TcbAcc_AI_assms]:
  "\<lbrace>valid_objs and obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_ipc_buffer tcb = v) t\<rbrace>
     get_cap (t, tcb_cnode_index 4)
   \<lbrace>\<lambda>rv s. valid_ipc_buffer_cap rv v\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule(1) cte_wp_tcb_cap_valid)
  apply (clarsimp simp add: tcb_cap_valid_def obj_at_def)
  apply (simp add: valid_ipc_buffer_cap_def mask_cap_def cap_rights_update_def
                   acap_rights_update_def is_tcb
            split: cap.split_asm arch_cap.split_asm)
  done



lemma pred_tcb_cap_wp_at [TcbAcc_AI_assms]:
  "\<lbrakk>pred_tcb_at proj P t s; valid_objs s;
    ref \<in> dom tcb_cap_cases;
    \<forall>cap. (pred_tcb_at proj P t s \<and> tcb_cap_valid cap (t, ref) s) \<longrightarrow> Q cap\<rbrakk> \<Longrightarrow>
   cte_wp_at Q (t, ref) s"
  apply (clarsimp simp: cte_wp_at_cases tcb_at_def dest!: get_tcb_SomeD)
  apply (rename_tac getF setF restr)
  apply (clarsimp simp: tcb_cap_valid_def pred_tcb_at_def obj_at_def)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def)
  apply (erule_tac x="(getF, setF, restr)" in ballE)
   apply fastforce+
  done

lemma as_user_hyp_refs_of[wp, TcbAcc_AI_assms]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
     as_user t m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_hyp_refs_trivial | simp)+
  done

lemmas sts_typ_ats = sts_typ_ats abs_atyp_at_lifts [OF set_thread_state_typ_at]

lemma arch_tcb_context_set_eq_RISCV64[TcbAcc_AI_assms]: "arch_tcb_context_set (arch_tcb_context_get t) t = t"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma arch_tcb_context_get_eq_RISCV64[TcbAcc_AI_assms]: "arch_tcb_context_get (arch_tcb_context_set uc t) = uc"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma arch_tcb_update_aux2: "(\<lambda>tcb. tcb\<lparr> tcb_arch := f (tcb_arch tcb) \<rparr>)  = tcb_arch_update f"
  by (rule ext, simp)

lemma arch_tcb_update_aux3: "tcb\<lparr>tcb_arch := f (tcb_arch tcb)\<rparr>  = tcb_arch_update f tcb"
  by(simp)

lemma tcb_context_update_aux: "arch_tcb_context_set (P (arch_tcb_context_get atcb)) atcb
                               = tcb_context_update (\<lambda>ctx. P ctx) atcb"
  by (simp add: arch_tcb_context_set_def arch_tcb_context_get_def)

end

global_interpretation TcbAcc_AI?: TcbAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact TcbAcc_AI_assms)?)
  qed

end
