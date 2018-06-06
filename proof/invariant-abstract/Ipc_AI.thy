(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Ipc_AI
imports "./$L4V_ARCH/ArchFinalise_AI"
begin

context begin interpretation Arch .
requalify_consts
  in_device_frame
requalify_facts
  set_mi_invs
  as_user_hyp_refs_of
end

declare set_mi_invs[wp]
declare as_user_hyp_refs_of[wp]

declare if_cong[cong del]

lemmas lookup_slot_wrapper_defs[simp] =
   lookup_source_slot_def lookup_target_slot_def lookup_pivot_slot_def

lemma get_mi_inv[wp]: "\<lbrace>I\<rbrace> get_message_info a \<lbrace>\<lambda>x. I\<rbrace>"
  by (simp add: get_message_info_def user_getreg_inv | wp)+

lemma set_mi_tcb [wp]:
  "\<lbrace> tcb_at t \<rbrace> set_message_info receiver msg \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: set_message_info_def) wp

lemma lsfco_cte_at:
  "\<lbrace>valid_objs and valid_cap cn\<rbrace>
  lookup_slot_for_cnode_op f cn idx depth
  \<lbrace>\<lambda>rv. cte_at rv\<rbrace>,-"
  by (rule hoare_post_imp_R, rule lookup_cnode_slot_real_cte, simp add: real_cte_at_cte)

declare do_machine_op_tcb[wp]

lemma load_ct_inv[wp]:
  "\<lbrace>P\<rbrace> load_cap_transfer buf \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: load_cap_transfer_def)
  apply (wp dmo_inv mapM_wp' loadWord_inv)
  done

lemma get_recv_slot_inv[wp]:
  "\<lbrace> P \<rbrace> get_receive_slots receiver buf \<lbrace>\<lambda>rv. P \<rbrace>"
  apply (case_tac buf)
   apply simp
  apply (simp add: split_def whenE_def)
  apply (wp | simp)+
  done

lemma cte_wp_at_eq_simp:
  "cte_wp_at (op = cap) = cte_wp_at (\<lambda>c. c = cap)"
  apply (rule arg_cong [where f=cte_wp_at])
  apply (safe intro!: ext)
  done

lemma get_rs_cte_at[wp]:
  "\<lbrace>\<top>\<rbrace>
  get_receive_slots receiver recv_buf
  \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at (\<lambda>c. c = cap.NullCap) x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp,wp,simp)
  apply (clarsimp simp add: split_def whenE_def)
  apply (wp | simp add: cte_wp_at_eq_simp | rule get_cap_wp)+
  done

lemma get_rs_cte_at2[wp]:
  "\<lbrace>\<top>\<rbrace>
  get_receive_slots receiver recv_buf
  \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. cte_wp_at (op = cap.NullCap) x s\<rbrace>"
  apply (rule hoare_strengthen_post, rule get_rs_cte_at)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma get_rs_real_cte_at[wp]:
  "\<lbrace>valid_objs\<rbrace>
   get_receive_slots receiver recv_buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. real_cte_at x s\<rbrace>"
  apply (cases recv_buf)
   apply (simp,wp,simp)
  apply (clarsimp simp add: split_def whenE_def)
  apply (wp hoare_drop_imps lookup_cnode_slot_real_cte lookup_cap_valid | simp | rule get_cap_wp)+
  done

declare returnOKE_R_wp [wp]

lemma cap_derive_not_null_helper:
  "\<lbrace>P\<rbrace> derive_cap slot cap \<lbrace>Q\<rbrace>,- \<Longrightarrow>
   \<lbrace>\<lambda>s. cap \<noteq> cap.NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> cap.IRQControlCap \<longrightarrow> P s\<rbrace>
     derive_cap slot
       cap
   \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> Q rv s\<rbrace>,-"
  apply (case_tac cap,
         simp_all add: is_zombie_def,
         safe elim!: hoare_post_imp_R)
   apply (wp | simp add: derive_cap_def is_zombie_def)+
  done

lemma mask_cap_Null [simp]:
  "(mask_cap R c = cap.NullCap) = (c = cap.NullCap)"
  by (cases c) (auto simp: mask_cap_def cap_rights_update_def)

lemma ensure_no_children_wp:
  "\<lbrace>\<lambda>s. descendants_of p (cdt s) = {} \<longrightarrow> P s\<rbrace> ensure_no_children p \<lbrace>\<lambda>_. P\<rbrace>, -"
  apply (simp add: ensure_no_children_descendants valid_def validE_R_def validE_def)
  apply (auto simp: in_monad)
  done

definition
  "valid_message_info mi \<equiv>
     mi_length mi \<le> of_nat msg_max_length \<and>
     mi_extra_caps mi \<le> of_nat msg_max_extra_caps"

(* FIXME: can some of these assumptions be proved with lifting lemmas? *)
locale Ipc_AI =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  fixes some_t :: "'t itself"
  assumes derive_cap_is_derived:
    "\<And>c' slot.
      \<lbrace>\<lambda>s::'state_ext state. c'\<noteq> cap.NullCap \<longrightarrow>
            cte_wp_at (\<lambda>cap. cap_master_cap cap = cap_master_cap c'
                           \<and> (cap_badge cap, cap_badge c') \<in> capBadge_ordering False
                           \<and> cap_asid cap = cap_asid c'
                           \<and> vs_cap_ref cap = vs_cap_ref c') slot s
                           \<and> valid_objs s\<rbrace>
        derive_cap slot c'
      \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> cte_wp_at (is_derived (cdt s) slot rv) slot s\<rbrace>, -"
  assumes is_derived_cap_rights [simp]:
    "\<And>m p R c. is_derived m p (cap_rights_update R c) = is_derived m p c"
  assumes data_to_message_info_valid:
    "\<And>w. valid_message_info (data_to_message_info w)"
  assumes get_extra_cptrs_length[wp]:
    "\<And>mi buf.
      \<lbrace>\<lambda>s::'state_ext state. valid_message_info mi\<rbrace>
         get_extra_cptrs buf mi
      \<lbrace>\<lambda>rv s. length rv \<le> msg_max_extra_caps\<rbrace>"
  assumes cap_asid_rights_update [simp]:
    "\<And>R c. cap_asid (cap_rights_update R c) = cap_asid c"
  assumes cap_rights_update_vs_cap_ref[simp]:
    "\<And>rs cap. vs_cap_ref (cap_rights_update rs cap) = vs_cap_ref cap"
  assumes is_derived_cap_rights2[simp]:
    "\<And>m p c R c'. is_derived m p c (cap_rights_update R c') = is_derived m p c c'"
  assumes cap_range_update [simp]:
    "\<And>R cap. cap_range (cap_rights_update R cap) = cap_range cap"
  assumes derive_cap_idle[wp]:
    "\<And>cap slot.
      \<lbrace>\<lambda>s::'state_ext state. global_refs s \<inter> cap_range cap = {}\<rbrace>
        derive_cap slot cap
      \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>, -"
  assumes arch_derive_cap_objrefs_iszombie:
    "\<And>P cap.
      \<lbrace>\<lambda>s::'state_ext state. P (set_option (aobj_ref cap)) False s\<rbrace>
        arch_derive_cap cap
      \<lbrace>\<lambda>rv s. P (set_option (aobj_ref rv)) False s\<rbrace>,-"
  assumes obj_refs_remove_rights[simp]:
    "\<And>rs cap. obj_refs (remove_rights rs cap) = obj_refs cap"
  assumes store_word_offs_vms[wp]:
    "\<And>ptr offs v.
      \<lbrace>valid_machine_state :: 'state_ext state \<Rightarrow> bool\<rbrace>
        store_word_offs ptr offs v
      \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  assumes is_zombie_update_cap_data[simp]:
    "\<And>P data cap. is_zombie (update_cap_data P data cap) = is_zombie cap"
  assumes valid_msg_length_strengthen:
    "\<And>mi. valid_message_info mi \<longrightarrow> unat (mi_length mi) \<le> msg_max_length"
  assumes copy_mrs_in_user_frame[wp]:
    "\<And>p t buf t' buf' n.
      \<lbrace>in_user_frame p :: 'state_ext state \<Rightarrow> bool\<rbrace>
        copy_mrs t buf t' buf' n
      \<lbrace>\<lambda>rv. in_user_frame p\<rbrace>"
  assumes make_arch_fault_msg_invs[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>invs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_aligned[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>pspace_aligned :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_distinct[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>pspace_distinct :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vmdb[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>valid_mdb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_ifunsafe[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_iflive[wp]:
    "\<And>ft t. make_arch_fault_msg  ft t \<lbrace>if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_state_refs_of[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s:: 'state_ext state. P (state_refs_of s)\<rbrace>"
  assumes make_arch_fault_msg_ct[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>cur_tcb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_zombies[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>zombies_final :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_it[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s :: 'state_ext state. P (idle_thread s)\<rbrace>"
  assumes make_arch_fault_msg_valid_globals[wp]:
    "\<And>ft t.   make_arch_fault_msg ft t \<lbrace>valid_global_refs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_idle[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_arch[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (arch_state s)\<rbrace>"
  assumes make_arch_fault_msg_typ_at[wp]:
    "\<And>P ft t T p. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>"
  assumes make_arch_fault_msg_irq_node[wp]:
    "\<And>P ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (interrupt_irq_node s)\<rbrace>"
  assumes make_arch_fault_msg_obj_at[wp]:
    "\<And> P P' pd ft t. make_arch_fault_msg ft t \<lbrace>\<lambda>s::'state_ext state. P (obj_at P' pd s)\<rbrace>"
  assumes make_arch_fault_msg_irq_handlers[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_irq_handlers :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vspace_objs[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_vspace_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_arch_caps[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_v_ker_map[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_eq_ker_map[wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_asid_map [wp]:
    "\<And>ft t. make_arch_fault_msg ft t \<lbrace>valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_only_idle [wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>only_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_pspace_in_kernel_window[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_refs_in_kernel_window[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_objs[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_global_objs[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_global_vspace_mappings[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_ioc[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_ioc :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_vms[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_machine_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_st_tcb_at'[wp]:
    "\<And> P p ft t . make_arch_fault_msg ft t \<lbrace>st_tcb_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_to[wp]:
    "\<And> ft t p. make_arch_fault_msg ft t \<lbrace>ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_valid_irq_states[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>valid_irq_states :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_cap_refs_respects_device_region[wp]:
    "\<And> ft t. make_arch_fault_msg ft t \<lbrace>cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes make_arch_fault_msg_pred_tcb[wp]:
    "\<And> P (proj :: itcb \<Rightarrow> 't) ft t . make_arch_fault_msg ft t \<lbrace>pred_tcb_at proj P t :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes do_fault_transfer_invs[wp]:
    "\<And>receiver badge sender recv_buf.
      \<lbrace>invs and tcb_at receiver :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_fault_transfer badge sender receiver recv_buf
      \<lbrace>\<lambda>rv. invs\<rbrace>"
  assumes lookup_ipc_buffer_in_user_frame[wp]:
    "\<And>t b.
      \<lbrace>valid_objs and tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
        lookup_ipc_buffer b t
      \<lbrace>case_option (\<lambda>_. True) in_user_frame\<rbrace>"
  assumes do_normal_transfer_non_null_cte_wp_at:
    "\<And>P ptr st send_buffer ep b gr rt recv_buffer.
      (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c) \<Longrightarrow>
        \<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
          do_normal_transfer st send_buffer ep b gr rt recv_buffer
        \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  assumes do_ipc_transfer_tcb_caps:
    "\<And>P t ref st ep b gr rt.
      (\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c) \<Longrightarrow>
        \<lbrace>valid_objs and cte_wp_at P (t, ref) and tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
          do_ipc_transfer st ep b gr rt
        \<lbrace>\<lambda>rv. cte_wp_at P (t, ref)\<rbrace>"
  assumes handle_arch_fault_reply_typ_at[wp]:
    "\<And> P T p x4 t label msg.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        handle_arch_fault_reply x4 t label msg
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
 assumes do_fault_transfer_cte_wp_at[wp]:
  "\<And> P p x t label msg.
      \<lbrace>cte_wp_at P p :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_fault_transfer x t label msg
      \<lbrace> \<lambda>rv. cte_wp_at P p \<rbrace>"
  assumes transfer_caps_loop_valid_vspace_objs:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_vspace_objs::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  assumes arch_get_sanitise_register_info_typ_at[wp]:
  "\<And> P T p t.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        arch_get_sanitise_register_info t
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"


context Ipc_AI begin

lemma is_derived_mask [simp]:
  "is_derived m p (mask_cap R c) = is_derived m p c"
  by (simp add: mask_cap_def)

lemma is_derived_remove_rights [simp]:
  "is_derived m p (remove_rights R c) = is_derived m p c"
  by (simp add: remove_rights_def)

lemma get_mi_valid[wp]:
  "\<lbrace>valid_mdb\<rbrace> get_message_info a \<lbrace>\<lambda>rv s. valid_message_info rv\<rbrace>"
  apply (simp add: get_message_info_def)
  apply (wp | simp add: data_to_message_info_valid)+
  done

end

crunch inv[wp]: get_extra_cptr P (wp: dmo_inv loadWord_inv)
crunch pspace_respects_device_region[wp]: set_extra_badge "pspace_respects_device_region"
  (wp: crunch_wps pspace_respects_device_region_dmo)

crunch cap_refs_respects_device_region[wp]: set_extra_badge "cap_refs_respects_device_region"
  (wp: crunch_wps cap_refs_respects_device_region_dmo)

lemma get_extra_cptrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_extra_cptrs buf mi \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (cases buf, simp_all del: upt.simps)
  apply (wp mapM_wp' dmo_inv loadWord_inv
             | simp add: load_word_offs_def del: upt.simps)+
  done

lemma mapM_length[wp]:
  "\<lbrace>\<lambda>s. P (length xs)\<rbrace> mapM f xs \<lbrace>\<lambda>rv s. P (length rv)\<rbrace>"
  by (induct xs arbitrary: P) (wpsimp simp: mapM_Cons mapM_def sequence_def|assumption)+

lemma cap_badge_rights_update[simp]:
  "cap_badge (cap_rights_update rights cap) = cap_badge cap"
  by (simp add: cap_rights_update_def split: cap.split)

lemma get_cap_cte_wp_at_rv:
  "\<lbrace>cte_wp_at (\<lambda>cap. P cap cap) p\<rbrace> get_cap p \<lbrace>\<lambda>rv. cte_wp_at (P rv) p\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma lsfco_cte_wp_at_univ:
  "\<lbrace>valid_objs and valid_cap croot and K (\<forall>cap rv. P cap rv)\<rbrace>
      lookup_slot_for_cnode_op f croot idx depth
   \<lbrace>\<lambda>rv. cte_wp_at (P rv) rv\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_post_imp_R)
   apply (rule lsfco_cte_at)
  apply (clarsimp simp: cte_wp_at_def)
  done


lemma bits_low_high_eq:
  assumes low: "x && mask bits = y && mask bits"
  and    high: "x >> bits = y >> bits"
  shows        "x = y"
  apply (rule word_eqI[rule_format])
  apply (case_tac "n < bits")
   apply (cut_tac x=n in word_eqD[OF low])
   apply (simp add: word_size)
  apply (cut_tac x="n - bits" in word_eqD[OF high])
  apply (simp add: nth_shiftr)
  done

context Ipc_AI begin
lemma mask_cap_vs_cap_ref[simp]:
  "vs_cap_ref (mask_cap msk cap) = vs_cap_ref cap"
  by (simp add: mask_cap_def)
end

lemma set_extra_badge_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (simp add: set_extra_badge_def store_word_offs_def | wp)+

lemmas set_extra_badge_typ_ats[wp] = abs_typ_at_lifts[OF set_extra_badge_typ_at]

crunch valid_objs [wp]: set_extra_badge valid_objs

crunch aligned [wp]: set_extra_badge pspace_aligned

crunch dist [wp]: set_extra_badge pspace_distinct

crunch valid_mdb [wp]: set_extra_badge valid_mdb

crunch cte_wp_at [wp]: set_extra_badge "cte_wp_at P p"

lemma impEM:
  "\<lbrakk>P \<longrightarrow> Q; P; \<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by auto

lemma derive_cap_is_derived_foo:
  "\<lbrace>\<lambda>s. \<forall>cap'. (cte_wp_at (\<lambda>capa.
                 cap_master_cap capa = cap_master_cap cap \<and>
                 (cap_badge capa, cap_badge cap) \<in> capBadge_ordering False \<and>
                 cap_asid capa = cap_asid cap \<and> vs_cap_ref capa = vs_cap_ref cap)
      slot s \<and> valid_objs s \<and> cap' \<noteq> NullCap
          \<longrightarrow> cte_at slot s )
            \<and> (s \<turnstile> cap \<longrightarrow> s \<turnstile> cap')
            \<and> (cap' \<noteq> NullCap \<longrightarrow> cap \<noteq> NullCap \<and> \<not> is_zombie cap \<and> cap \<noteq> IRQControlCap)
          \<longrightarrow> Q cap' s \<rbrace>
      derive_cap slot cap \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp add: validE_R_def validE_def valid_def
                     split: sum.splits)
  apply (frule in_inv_by_hoareD[OF derive_cap_inv], clarsimp)
  apply (erule allE)
  apply (erule impEM)
   apply (frule use_validE_R[OF _ cap_derive_not_null_helper, OF _ _ imp_refl])
    apply (wp derive_cap_inv)
    apply (intro conjI)
     apply (clarsimp simp:cte_wp_at_caps_of_state)+
     apply (erule(1) use_validE_R[OF _ derive_cap_valid_cap])
    apply simp
  apply simp
  done

lemma cap_rights_update_NullCap[simp]:
  "(cap_rights_update rs cap = cap.NullCap) = (cap = cap.NullCap)"
  by (simp add: cap_rights_update_def split: cap.split)

crunch in_user_frame[wp]: set_extra_badge "in_user_frame buffer"
crunch in_device_frame[wp]: set_extra_badge "in_device_frame buffer"

lemma cap_insert_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at (is_derived (cdt s) src cap) src s \<and> valid_mdb s \<and> valid_objs s
    \<and> (if p = dest then P cap else cte_wp_at (\<lambda>c. P (masked_as_full c cap)) p s)\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:if_split_asm)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
     apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
    apply (wp get_cap_wp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp:cap_insert_def)
  apply (wp set_cap_cte_wp_at | simp split del: if_split)+
    apply (clarsimp simp:set_untyped_cap_as_full_def split del:if_splits)
   apply (wp set_cap_cte_wp_at get_cap_wp)+
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid)
  apply (intro conjI impI)
    apply (clarsimp simp:masked_as_full_def split:if_splits)+
   apply (clarsimp simp:valid_mdb_def is_derived_def)
   apply (drule(4) untyped_incD)
   apply (clarsimp simp:is_cap_simps cap_aligned_def
      dest!:valid_cap_aligned split:if_split_asm)
    apply (drule_tac y = "of_nat fa" in word_plus_mono_right[OF _ is_aligned_no_overflow',rotated])
     apply (simp add:word_of_nat_less)
    apply (clarsimp simp:p_assoc_help)
   apply (drule(1) caps_of_state_valid)+
   apply (clarsimp simp:valid_cap_def valid_untyped_def max_free_index_def)
  apply (clarsimp simp:masked_as_full_def split:if_splits)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
  apply (erule impEM)
    apply (clarsimp simp: is_derived_def split:if_splits)
     apply (clarsimp simp:is_cap_simps cap_master_cap_simps)
   apply (clarsimp simp:is_cap_simps cap_master_cap_simps dest!:cap_master_cap_eqDs)
   apply (clarsimp simp:is_derived_def is_cap_simps cap_master_cap_simps)
  done

lemma cap_insert_weak_cte_wp_at2:
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not>is_untyped_cap c"
  shows
  "\<lbrace>\<lambda>s. if p = dest then P cap else cte_wp_at P p s\<rbrace>
   cap_insert cap src dest
   \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  unfolding cap_insert_def
  by (wp set_cap_cte_wp_at get_cap_wp static_imp_wp
      | simp add: cap_insert_def
      | unfold set_untyped_cap_as_full_def
      | auto simp: cte_wp_at_def dest!:imp)+

crunch in_user_frame[wp]: cap_insert "in_user_frame buffer"
  (wp: crunch_wps ignore: get_cap)

crunch cdt [wp]: set_extra_badge "\<lambda>s. P (cdt s)"

lemma descendants_insert_update:
  "\<lbrakk>m dest = None; p \<in> descendants_of a m\<rbrakk>
   \<Longrightarrow> p \<in> descendants_of a (\<lambda>x. if x = dest then y else m x)"
  apply (clarsimp simp:descendants_of_empty descendants_of_def)
  apply (simp add:cdt_parent_rel_def)
  apply (erule trancl_mono)
  apply (clarsimp simp:is_cdt_parent_def)
  done

lemma masked_as_full_null_cap[simp]:
  "(masked_as_full x x = cap.NullCap) = (x = cap.NullCap)"
  "(cap.NullCap  = masked_as_full x x) = (x = cap.NullCap)"
  by (case_tac x,simp_all add:masked_as_full_def)+

lemma transfer_caps_loop_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  apply (induct caps arbitrary: n slots mi)
   apply simp
   apply wp
   apply simp
  apply (clarsimp split del: if_split)
  apply (rule hoare_pre)
   apply (wp const_on_failure_wp hoare_drop_imps | assumption)+
  apply simp
  done

lemma valid_remove_rights_If[simp]:
  "valid_cap cap s \<Longrightarrow> valid_cap (if P then remove_rights rs cap else cap) s"
  by simp

declare const_on_failure_wp [wp]

crunch ex_cte_cap_wp_to [wp]: set_extra_badge "ex_cte_cap_wp_to P p"
  (rule: ex_cte_cap_to_pres)

lemma cap_insert_assume_null:
  "\<lbrace>P\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. cte_wp_at (op = cap.NullCap) dest s \<longrightarrow> P s\<rbrace> cap_insert cap src dest \<lbrace>Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (erule impCE)
   apply (simp add: cap_insert_def)
   apply (rule hoare_seq_ext[OF _ get_cap_sp])+
   apply (clarsimp simp: valid_def cte_wp_at_caps_of_state in_monad
              split del: if_split)
  apply (erule hoare_pre(1))
  apply simp
  done

context Ipc_AI begin

lemma transfer_caps_loop_presM:
  fixes P vo em ex buffer slots caps n mi
  assumes x: "\<And>cap src dest.
              \<lbrace>\<lambda>s::'state_ext state.
                               P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> real_cte_at dest s \<and> s \<turnstile> cap \<and> tcb_cap_valid cap dest s
                                   \<and> real_cte_at src s
                                   \<and> cte_wp_at (is_derived (cdt s) src cap) src s \<and> cap \<noteq> cap.NullCap)
                       \<and> (em \<longrightarrow> cte_wp_at (op = cap.NullCap) dest s)
                       \<and> (ex \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) dest s)\<rbrace>
                 cap_insert cap src dest \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes eb: "\<And>b n. \<lbrace>P\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. P\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> (vo \<longrightarrow> valid_objs s \<and> valid_mdb s \<and> distinct slots \<and>
                                 (\<forall>x \<in> set slots.  cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s \<and> real_cte_at x s) \<and>
                                 (\<forall>x \<in> set caps. valid_cap (fst x) s \<and>
                                  cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp \<noteq> fst x \<longrightarrow> cp = masked_as_full (fst x) (fst x)) (snd x) s
                                           \<and> real_cte_at (snd x) s))
                       \<and> (ex \<longrightarrow> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s))\<rbrace>
                  transfer_caps_loop ep buffer n caps slots mi
              \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (induct caps arbitrary: slots n mi)
   apply (simp, wp, simp)
  apply (clarsimp simp add: Let_def split_def whenE_def
                      cong: if_cong list.case_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp eb hoare_vcg_const_imp_lift hoare_vcg_const_Ball_lift static_imp_wp
           | assumption | simp split del: if_split)+
      apply (rule cap_insert_assume_null)
      apply (wp x hoare_vcg_const_Ball_lift cap_insert_cte_wp_at static_imp_wp)+
      apply (rule hoare_vcg_conj_liftE_R)
       apply (rule derive_cap_is_derived_foo)
      apply (rule_tac Q' ="\<lambda>cap' s. (vo \<longrightarrow> cap'\<noteq> cap.NullCap \<longrightarrow>
          cte_wp_at (is_derived (cdt s) (aa, b) cap') (aa, b) s)
          \<and> (cap'\<noteq> cap.NullCap \<longrightarrow> QM s cap')" for QM
          in hoare_post_imp_R)
        prefer 2
        apply clarsimp
        apply assumption
       apply (rule hoare_vcg_conj_liftE_R)
         apply (rule hoare_vcg_const_imp_lift_R)
        apply (rule derive_cap_is_derived)
      apply (wp derive_cap_is_derived_foo)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_cnode_always_appropriate_strg
                        real_cte_tcb_valid caps_of_state_valid
             split del: if_split)
  apply (clarsimp simp: remove_rights_def caps_of_state_valid
                        neq_Nil_conv cte_wp_at_caps_of_state
                        imp_conjR[symmetric] conj_comms
                 split del: if_split)
  apply (intro conjI)
   apply clarsimp
   apply (case_tac "cap = a",clarsimp)
   apply (clarsimp simp:masked_as_full_def is_cap_simps)
   apply (clarsimp simp: cap_master_cap_simps split:if_splits)
  apply (clarsimp split del: if_split)
  apply (intro conjI)
    apply (clarsimp split: if_split)
   apply (clarsimp)
  apply (rule ballI)
  apply (drule(1) bspec)
  apply clarsimp
  apply (intro conjI)
   apply (case_tac "capa = ac",clarsimp+)
  apply (case_tac "capa = ac")
   apply (clarsimp simp:masked_as_full_def is_cap_simps split:if_splits)+
  done

end

abbreviation (input)
  "transfer_caps_srcs caps s \<equiv>
    (\<forall>x \<in> set caps. cte_wp_at (\<lambda>cp. fst x \<noteq> cap.NullCap \<longrightarrow> cp = fst x) (snd x) s
                                           \<and> real_cte_at (snd x) s)"

context Ipc_AI begin

lemmas transfer_caps_loop_pres =
    transfer_caps_loop_presM[where vo=False and ex=False and em=False, simplified]

lemma transfer_caps_loop_typ_at[wp]:
   "\<And>P T p ep buffer n caps slots mi.
      \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
        transfer_caps_loop ep buffer n caps slots mi
      \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_aligned[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_aligned :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
     \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma transfer_loop_distinct[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_distinct :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma invs_valid_objs2:
  "\<And>s. invs s \<longrightarrow> valid_objs s"
  by clarsimp

lemma transfer_caps_loop_valid_objs[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_objs and valid_mdb and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
            and transfer_caps_srcs caps and K (distinct slots) :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
    apply (wp|clarsimp)+
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
   apply clarsimp+
  done

lemma transfer_caps_loop_valid_mdb[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>\<lambda>s. valid_mdb s \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s
         \<and> (\<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
         \<and> transfer_caps_srcs caps s \<and> distinct slots\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_mdb :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=True and ex=False])
    apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (wp set_extra_badge_valid_mdb)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec)+
  apply clarsimp
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
   apply clarsimp+
  done

crunch state_refs_of [wp]: set_extra_badge "\<lambda>s. P (state_refs_of s)"
crunch state_hyp_refs_of [wp]: set_extra_badge "\<lambda>s. P (state_hyp_refs_of s)"

lemma tcl_state_refs_of[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (state_refs_of s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma tcl_state_hyp_refs_of[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch if_live [wp]: set_extra_badge if_live_then_nonz_cap

lemma tcl_iflive[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_iflive)

crunch if_unsafe [wp]: set_extra_badge if_unsafe_then_cap

lemma tcl_ifunsafe[wp]:
  "\<And>slots ep buffer n caps mi.
    \<lbrace>\<lambda>s::'state_ext state. if_unsafe_then_cap s
                             \<and> (\<forall>x\<in>set slots. ex_cte_cap_wp_to is_cnode_cap x s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wp transfer_caps_loop_presM[where vo=False and em=False and ex=True, simplified]
            cap_insert_ifunsafe | simp)+

end

lemma get_cap_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> get_cap p \<lbrace>\<lambda>c s. global_refs s \<inter> cap_range c = {}\<rbrace>"
  apply (rule hoare_pre)
   apply (rule get_cap_wp)
  apply (clarsimp simp: valid_refs_def2 valid_global_refs_def cte_wp_at_caps_of_state)
  by blast

crunch pred_tcb_at [wp]: set_extra_badge "\<lambda>s. pred_tcb_at proj P p s"
crunch idle [wp]: set_extra_badge "\<lambda>s. P (idle_thread s)"

lemma (in Ipc_AI) tcl_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_idle::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_idle valid_idle_lift)

crunch cur_tcb [wp]: set_extra_badge cur_tcb

lemma (in Ipc_AI) tcl_ct[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>cur_tcb::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch it[wp]: cap_insert "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma (in Ipc_AI) tcl_it[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (idle_thread s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  by (wp transfer_caps_loop_pres)

lemma (in Ipc_AI) derive_cap_objrefs_iszombie:
  "\<And>cap P slot.
    \<lbrace>\<lambda>s::'state_ext state. \<not> is_zombie cap \<longrightarrow> P (obj_refs cap) False s\<rbrace>
      derive_cap slot cap
    \<lbrace>\<lambda>rv s. rv \<noteq> cap.NullCap \<longrightarrow> P (obj_refs rv) (is_zombie rv) s\<rbrace>,-"
  including no_pre
  apply (case_tac cap, simp_all add: derive_cap_def is_zombie_def)
          apply (rule hoare_pre,
                 (wp | simp add: o_def arch_derive_cap_objrefs_iszombie)+)+
  done

lemma is_zombie_rights[simp]:
  "is_zombie (remove_rights rs cap) = is_zombie cap"
  by (simp add: is_zombie_def remove_rights_def cap_rights_update_def
         split: cap.splits)

crunch caps_of_state [wp]: set_extra_badge "\<lambda>s. P (caps_of_state s)"

lemma set_extra_badge_zombies_final[wp]:
  "\<lbrace>zombies_final\<rbrace> set_extra_badge buffer b n \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  apply (simp add: zombies_final_def cte_wp_at_caps_of_state is_final_cap'_def2)
  apply (wp hoare_vcg_all_lift final_cap_lift)
  done

lemma (in Ipc_AI) tcl_zombies[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>zombies_final and valid_objs and valid_mdb and K (distinct slots)
          and (\<lambda>s::'state_ext state. \<forall>slot \<in> set slots. real_cte_at slot s
                                     \<and> cte_wp_at (\<lambda>cap. cap = NullCap) slot s )
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
    apply (wp cap_insert_zombies)
    apply clarsimp
    apply (case_tac "(a, b) = (ab, bb)")
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def)
     apply (simp split: if_split_asm)
      apply ((clarsimp simp: is_cap_simps cap_master_cap_def
                     split: cap.split_asm)+)[2]
    apply (frule (3) zombies_finalD3)
     apply (clarsimp simp: is_derived_def is_cap_simps cap_master_cap_simps
                     split: if_split_asm dest!:cap_master_cap_eqDs)
     apply (drule_tac a=r in equals0D)
     apply (drule master_cap_obj_refs, simp)
    apply (fastforce simp: cte_wp_at_caps_of_state is_derived_def
                           is_cap_simps cap_master_cap_def
                    split: if_split_asm cap.split_asm)
   apply wp
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec,clarsimp)
  apply (fastforce dest!:caps_of_state_valid)
  done

lemmas derive_cap_valid_globals [wp]
  = derive_cap_inv[where P=valid_global_refs and slot = r and c = cap for r cap]

crunch arch [wp]: set_extra_badge "\<lambda>s. P (arch_state s)"

crunch irq [wp]: set_extra_badge "\<lambda>s. P (interrupt_irq_node s)"

context Ipc_AI begin

lemma transfer_caps_loop_valid_globals [wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_global_refs and valid_objs and valid_mdb and K (distinct slots)
       and (\<lambda>s::'state_ext state. \<forall>slot \<in> set slots. real_cte_at slot s
                                  \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
       and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=True])
     apply (wp | simp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range)
    apply (wp valid_global_refs_cte_lift|simp|intro conjI ballI)+
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  done

lemma transfer_caps_loop_arch[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (arch_state s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
  by (rule transfer_caps_loop_pres) wp+


lemma transfer_caps_loop_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> transfer_caps_loop ep buffer n caps slots mi \<lbrace>\<lambda>r s::'state_ext state. P (obj_at P' pd s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=False, simplified, where P="\<lambda>s. P (obj_at P' pd s)"])
    apply (wp cap_insert_aobj_at)
   apply (wpsimp simp: set_extra_badge_def)
  apply assumption
  done

lemma transfer_caps_loop_valid_arch[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_arch_state::'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_aobj_at; wp transfer_caps_loop_aobj_at)
(*
lemma tcl_reply':
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_reply_caps and valid_reply_masters and valid_objs and valid_mdb and K(distinct slots)
          and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_reply_caps and valid_reply_masters :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
     apply (clarsimp simp: real_cte_at_cte)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_def is_cap_simps)
     apply (frule(1) valid_reply_mastersD[OF caps_of_state_cteD])
     apply (frule(1) tcb_cap_valid_caps_of_stateD)
     apply (frule(1) caps_of_state_valid)
     apply (clarsimp simp: tcb_cap_valid_def valid_cap_def is_cap_simps)
     apply (clarsimp simp: obj_at_def is_tcb is_cap_table cap_master_cap_def)
    apply (wpsimp wp: valid_reply_caps_st_cte_lift valid_reply_masters_cte_lift)
    apply (clarsimp simp:cte_wp_at_caps_of_state | intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

lemmas tcl_reply[wp] = tcl_reply' [THEN hoare_strengthen_post
                                        [where R="\<lambda>_. valid_reply_caps"],
                                   simplified]

lemmas tcl_reply_masters[wp] = tcl_reply' [THEN hoare_strengthen_post
                                        [where R="\<lambda>_. valid_reply_masters"],
                                   simplified]
*)
lemma transfer_caps_loop_irq_node[wp]:
  "\<And>P ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. P (interrupt_irq_node s)\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  by (rule transfer_caps_loop_pres; wp)

lemma cap_master_cap_irqs:
  "\<And>cap. cap_irqs cap = (case cap_master_cap cap
           of cap.IRQHandlerCap irq \<Rightarrow> {irq}
              | _ \<Rightarrow> {})"
  by (simp add: cap_master_cap_def split: cap.split)


crunch irq_state [wp]: set_extra_badge "\<lambda>s. P (interrupt_states s)"

lemma transfer_caps_loop_irq_handlers[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_irq_handlers and valid_objs and valid_mdb and K (distinct slots)
         and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
         and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_irq_handlers :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=False and ex=False])
     apply wp
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_derived_def split: if_split_asm)
     apply (simp add: cap_master_cap_irqs)+
    apply (wp valid_irq_handlers_lift)
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI ballI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

crunch valid_arch_caps [wp]: set_extra_badge valid_arch_caps


lemma transfer_caps_loop_valid_arch_caps[wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>valid_arch_caps and valid_objs and valid_mdb and K(distinct slots)
           and (\<lambda>s. \<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
           and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_arch_caps :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (wp transfer_caps_loop_presM[where vo=True and em=False and ex=False]
            cap_insert_valid_arch_caps)
     apply simp
    apply wp
   apply (clarsimp simp:cte_wp_at_caps_of_state|intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done

crunch valid_global_objs [wp]: set_extra_badge valid_global_objs


lemma transfer_caps_loop_valid_global_objs[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_objs :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  by (wp transfer_caps_loop_pres cap_insert_valid_global_objs)

crunch valid_kernel_mappings [wp]: set_extra_badge valid_kernel_mappings


lemma transfer_caps_loop_v_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch equal_kernel_mappings [wp]: set_extra_badge equal_kernel_mappings


lemma transfer_caps_loop_eq_ker_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch valid_asid_map [wp]: set_extra_badge valid_asid_map


lemma transfer_caps_loop_asid_map[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_asid_map :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+


crunch only_idle [wp]: set_extra_badge only_idle


lemma transfer_caps_loop_only_idle[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>only_idle :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp transfer_caps_loop_pres | simp)+

crunch valid_global_vspace_mappings [wp]: set_extra_badge valid_global_vspace_mappings


lemma transfer_caps_loop_valid_global_pd_mappings[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch pspace_in_kernel_window [wp]: set_extra_badge pspace_in_kernel_window


lemma transfer_caps_loop_pspace_in_kernel_window[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (wp transfer_caps_loop_pres)


crunch cap_refs_in_kernel_window[wp]: set_extra_badge cap_refs_in_kernel_window

lemma transfer_caps_loop_cap_refs_in_kernel_window [wp]:
  "\<And>slots caps ep buffer n mi.
    \<lbrace>cap_refs_in_kernel_window and valid_objs and valid_mdb and K (distinct slots)
          and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s )
          and transfer_caps_srcs caps\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  apply (rule hoare_pre)
  apply (rule transfer_caps_loop_presM[where em=False and ex=False and vo=True])
     apply (wp | simp)+
     apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range)
    apply (wp | simp)+
  apply (clarsimp simp:cte_wp_at_caps_of_state | intro conjI)+
   apply (drule(1) bspec,clarsimp)
   apply (frule(1) caps_of_state_valid)
   apply (fastforce simp:valid_cap_def)
  apply (drule(1) bspec)
  apply clarsimp
  done


crunch valid_ioc[wp]: store_word_offs valid_ioc


lemma transfer_caps_loop_valid_ioc[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_ioc s\<rbrace>
     transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (wp transfer_caps_loop_pres | simp add: set_extra_badge_def)+


lemma set_extra_badge_vms[wp]:
  "\<And>buffer b n.
    \<lbrace>valid_machine_state::'state_ext state \<Rightarrow> bool\<rbrace>
      set_extra_badge buffer b n
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: set_extra_badge_def) wp


lemma transfer_caps_loop_vms[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_machine_state s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (wp transfer_caps_loop_pres)

crunch valid_irq_states[wp]: set_extra_badge "valid_irq_states"
  (ignore: do_machine_op)


lemma transfer_caps_loop_valid_irq_states[wp]:
  "\<And>ep buffer n caps slots mi.
    \<lbrace>\<lambda>s::'state_ext state. valid_irq_states s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  by (wp transfer_caps_loop_pres)


lemma transfer_caps_respects_device_region[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. pspace_respects_device_region s\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>_. pspace_respects_device_region\<rbrace>"
  apply (wp transfer_caps_loop_pres)
  done

lemma transfer_caps_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region and valid_objs and valid_mdb and (\<lambda>s. \<forall>slot \<in> set slots. real_cte_at slot s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) slot s)
            and transfer_caps_srcs caps and K (distinct slots)\<rbrace>
    transfer_caps_loop ep buffer n caps slots mi
   \<lbrace>\<lambda>_ s::'state_ext state. cap_refs_respects_device_region s\<rbrace>"
  apply (rule hoare_pre)
   apply (rule transfer_caps_loop_presM[where vo=True and em=True and ex=False])
    apply wp
    apply (clarsimp simp: cte_wp_at_caps_of_state is_derived_cap_range is_derived_cap_is_device)
   apply (wp set_extra_badge_valid_mdb)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) bspec)+
  apply clarsimp
  apply (drule(1) caps_of_state_valid)
  apply (case_tac "a = cap.NullCap")
  apply clarsimp+
  done

lemma transfer_caps_loop_invs[wp]:
  "\<And>slots.
    \<lbrace>\<lambda>s::'state_ext state. invs s
          \<and> (\<forall>x \<in> set slots. ex_cte_cap_wp_to is_cnode_cap x s) \<and> distinct slots
          \<and> (\<forall>x \<in> set slots. real_cte_at x s \<and> cte_wp_at (\<lambda>cap. cap = cap.NullCap) x s)
          \<and> transfer_caps_srcs caps s\<rbrace>
      transfer_caps_loop ep buffer n caps slots mi
    \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_irq_node_typ transfer_caps_loop_valid_vspace_objs)

end

(* FIXME: move *)
crunch valid_vspace_objs [wp]: set_extra_badge valid_vspace_objs

crunch vspace_objs [wp]: set_untyped_cap_as_full "valid_vspace_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object set_cap)

crunch vspace_objs [wp]: cap_insert "valid_vspace_objs"
  (wp: crunch_wps simp: crunch_simps ignore: set_object set_cap)

lemma zipWith_append2:
  "length ys + 1 < n \<Longrightarrow>
   zipWith f [0 ..< n] (ys @ [y]) = zipWith f [0 ..< n] ys @ [f (length ys) y]"
  apply (simp add: zipWith_def zip_append2)
  apply (subst upt_conv_Cons, erule Suc_lessD)
  apply simp
  apply (subst zip_take_triv[OF order_refl, symmetric], fastforce)
  done

(* FIXME: move *)
lemma list_all2_zip_same:
  assumes rl: "\<And>a a' x y. P (x, a) (y, a) \<Longrightarrow> P (x, a') (y, a')"
  shows "list_all2 (\<lambda>x y. P (x, a) (y, a)) xs ys \<Longrightarrow> list_all2 P (zip xs as) (zip ys as)"
  apply (induct xs arbitrary: as ys a)
   apply simp
  apply (case_tac as)
   apply simp
  apply simp
  apply (case_tac ys)
   apply simp
  apply clarsimp
  apply (erule rl)
  done


lemma grs_distinct[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots t buf \<lbrace>\<lambda>rv s. distinct rv\<rbrace>"
  by (cases buf; wpsimp)


lemma transfer_caps_mi_label[wp]:
  "\<lbrace>\<lambda>s. P (mi_label mi)\<rbrace>
     transfer_caps mi caps ep receiver recv_buf
   \<lbrace>\<lambda>mi' s. P (mi_label mi')\<rbrace>"
  by (wpsimp simp: transfer_caps_def)


context Ipc_AI begin

lemma transfer_cap_typ_at[wp]:
  "\<And>P T p mi caps ep receiver recv_buf.
    \<lbrace>\<lambda>s::'state_ext state. P (typ_at T p s)\<rbrace>
      transfer_caps mi caps ep receiver recv_buf
    \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: cap_insert_typ_at hoare_drop_imps simp: transfer_caps_def)

lemma transfer_cap_tcb[wp]:
  "\<And>mi caps ep receiver recv_buf.
    \<lbrace>\<lambda>s::'state_ext state. tcb_at t s\<rbrace>
      transfer_caps mi caps ep receiver recv_buf
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

lemma cte_refs_mask[simp]:
  "cte_refs (mask_cap rs cap) = cte_refs cap"
  by (rule ext, cases cap, simp_all add: mask_cap_def cap_rights_update_def)


lemma get_cap_cte_caps_to[wp]:
  "\<lbrace>\<lambda>s. \<forall>cp. P cp = P cp\<rbrace>
     get_cap sl
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (cases sl, fastforce elim!: cte_wp_at_weakenE)
  done


lemma lookup_cap_cte_caps_to[wp]:
  "\<lbrace>\<lambda>s. \<forall>rs cp. P (mask_cap rs cp) = P cp\<rbrace>
     lookup_cap t cref
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>p\<in>cte_refs rv (interrupt_irq_node s). ex_cte_cap_wp_to P p s)\<rbrace>,-"
  by (simp add: lookup_cap_def split_def) wpsimp


lemma is_cnode_cap_mask[simp]:
  "is_cnode_cap (mask_cap rs cap) = is_cnode_cap cap"
  by (auto simp: mask_cap_def cap_rights_update_def
          split: cap.split)


lemma get_rs_cap_to[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots rcvr buf
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. ex_cte_cap_wp_to is_cnode_cap x s\<rbrace> "
  apply (cases buf, simp_all add: split_def whenE_def split del: if_split)
   apply (wp | simp | rule hoare_drop_imps)+
  done


lemma derive_cap_notzombie[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. \<not> is_zombie rv\<rbrace>,-"
  by (cases cap; wpsimp simp: derive_cap_def is_zombie_def o_def)


lemma derive_cap_notIRQ[wp]:
  "\<lbrace>\<top>\<rbrace> derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> cap.IRQControlCap\<rbrace>,-"
  by (cases cap; wpsimp simp: derive_cap_def o_def)


lemma get_cap_zombies_helper:
  "\<lbrace>zombies_final\<rbrace>
     get_cap p
   \<lbrace>\<lambda>rv s. \<not> is_zombie rv
     \<longrightarrow> (\<forall>r\<in>obj_refs rv. \<forall>p'.
           cte_wp_at (\<lambda>c. r \<in> obj_refs c) p' s
             \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) p' s)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_def)
  apply (subgoal_tac "p \<noteq> (a, b)")
   apply (drule(3) zombies_finalD2)
    apply blast
   apply simp
  apply clarsimp
  done

context Ipc_AI begin

lemma random_helper[simp]:
  "\<And>ct_send_data ct ms cap.
    is_zombie (case ct_send_data ct of None \<Rightarrow> mask_cap ms cap
                 | Some w \<Rightarrow> update_cap_data P w (mask_cap ms cap))
      = is_zombie cap"
  by (simp split: option.splits)

end

lemma zombies_final_pres:
  assumes x: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
      and y: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  shows      "\<lbrace>zombies_final\<rbrace> f \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp only: zombies_final_def final_cap_at_eq
                    imp_conv_disj cte_wp_at_neg2[where P=is_zombie]
                    de_Morgan_conj)
  apply (intro hoare_vcg_disj_lift hoare_vcg_ex_lift hoare_vcg_conj_lift
               y hoare_vcg_all_lift valid_cte_at_neg_typ x)
  done


lemma cte_wp_at_orth:
  "\<lbrakk> cte_wp_at (\<lambda>c. P c) p s; cte_wp_at (\<lambda>c. \<not> P c) p s \<rbrakk> \<Longrightarrow> False"
  unfolding cte_wp_at_def
  by clarsimp


declare sym_ex_elim[elim!]


lemma no_irq_case_option:
  "\<lbrakk> no_irq f; \<And>x. no_irq (g x) \<rbrakk> \<Longrightarrow> no_irq (case_option f g x)"
  apply (subst no_irq_def)
  apply clarsimp
  apply (rule hoare_pre, wpsimp wp: no_irq)
  apply assumption
  done


lemma get_mrs_inv[wp]:
  "\<lbrace>P\<rbrace> get_mrs t buf info \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp simp: get_mrs_def load_word_offs_def wp: dmo_inv loadWord_inv mapM_wp')


lemma copy_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: copy_mrs_def load_word_offs_def
                   store_word_offs_def set_object_def
              cong: option.case_cong
              split del: if_split)
  apply (wp hoare_vcg_split_case_option mapM_wp')
   apply (wp hoare_drop_imps mapM_wp')+
   apply simp_all
  done


lemmas copy_mrs_typ_ats[wp] = abs_typ_at_lifts[OF copy_mrs_typ_at]


lemma copy_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma copy_mrs_ntfn_at[wp]:
  "\<lbrace> ntfn_at p \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. ntfn_at p \<rbrace>"
  by (simp add: ntfn_at_typ, wp)


lemmas copy_mrs_redux =
   copy_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

lemma store_word_offs_invs[wp]:
  "\<lbrace>invs\<rbrace> store_word_offs p x w \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wp | simp add: store_word_offs_def)+

lemma copy_mrs_invs[wp]:
  "\<lbrace> invs and tcb_at r and tcb_at s \<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. invs \<rbrace>"
  unfolding copy_mrs_redux by (wpsimp wp: mapM_wp')

lemma set_mrs_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_mrs t a msgs \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (cases a)
   apply (simp add: set_mrs_redux)
   apply (wp thread_set_valid_objs_triv)
       apply (auto simp: tcb_cap_cases_def)[1]
      apply (simp add: valid_arch_arch_tcb_context_set)+
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
            split del: if_split)
  apply (wp mapM_wp' thread_set_valid_objs_triv | simp)+
      apply (auto simp: tcb_cap_cases_def valid_arch_arch_tcb_context_set)
  done


lemma set_mrs_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace>  set_mrs t a msgs \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def
             cong: option.case_cong
              del: upt.simps)
  apply (wp mapM_wp' | wpcw | simp)+
  done


lemma copy_mrs_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc
       | simp add: store_word_offs_def load_word_offs_def)+
  done


lemma copy_mrs_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp' | wpc
       | simp add: store_word_offs_def load_word_offs_def)+
  done


lemma get_tcb_ko_at:
  "(get_tcb t s = Some tcb) = ko_at (TCB tcb) t s"
  by (auto simp: obj_at_def get_tcb_def
           split: option.splits Structures_A.kernel_object.splits)


lemmas get_tcb_ko_atI = get_tcb_ko_at [THEN iffD1]


crunch "distinct" [wp]: set_mrs pspace_distinct
  (wp: select_wp hoare_vcg_split_case_option mapM_wp
       hoare_drop_imps  refl
   simp: zipWithM_x_mapM)


crunch "distinct" [wp]: copy_mrs pspace_distinct
  (wp: mapM_wp' simp: copy_mrs_redux)


crunch mdb [wp]: store_word_offs valid_mdb (wp: crunch_wps simp: crunch_simps)


crunch caps_of_state [wp]: store_word_offs "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb_P [wp]: set_mrs "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


crunch mdb_R [wp]: set_mrs "\<lambda>s. P (is_original_cap s)"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)


lemma set_mrs_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_mrs t b m \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
             cong: option.case_cong
                split del: if_split)
  apply (wp mapM_wp' | wpc)+
  apply (wp thread_set_caps_of_state_trivial2 | simp)+
  done


lemma set_mrs_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (rule valid_mdb_lift; wp)


crunch mdb_P [wp]: copy_mrs "\<lambda>s. P (cdt s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb_R [wp]: copy_mrs "\<lambda>s. P (is_original_cap s)"
  (wp: crunch_wps simp: crunch_simps)


crunch mdb [wp]: copy_mrs valid_mdb
  (wp: crunch_wps simp: crunch_simps)


lemma set_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> set_mrs tcb buf msg \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)


lemma copy_mrs_ep_at[wp]:
  "\<lbrace>ep_at x\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. ep_at x\<rbrace>"
  by (simp add: ep_at_typ, wp)

crunch cte_wp_at[wp]: copy_mrs "cte_wp_at P p"
  (wp: crunch_wps)


crunch inv[wp]: lookup_extra_caps "P"
  (wp: crunch_wps mapME_wp' simp: crunch_simps ignore: mapME)

lemma lookup_extra_caps_srcs[wp]:
  "\<lbrace>valid_objs\<rbrace> lookup_extra_caps thread buf info \<lbrace>transfer_caps_srcs\<rbrace>,-"
  apply (simp add: lookup_extra_caps_def lookup_cap_and_slot_def
                   split_def lookup_slot_for_thread_def)
  apply (wp mapME_set[where R=valid_objs] get_cap_wp resolve_address_bits_real_cte_at
             | simp add: cte_wp_at_caps_of_state
             | wp_once hoare_drop_imps
             | clarsimp simp: objs_valid_tcb_ctable)+
  done


lemma mapME_length:
  "\<lbrace>\<lambda>s. P (length xs)\<rbrace> mapME m xs \<lbrace>\<lambda>ys s. P (length ys)\<rbrace>, -"
  apply (induct xs arbitrary: P)
   apply (simp add: mapME_Nil | wp)+
  apply (simp add: mapME_def sequenceE_def)
  apply (rule hoare_pre)
   apply (wp | simp | assumption)+
  done

context Ipc_AI begin

crunch typ_at[wp]: do_normal_transfer "\<lambda>s::'state_ext state. P (typ_at T p s)"

lemma do_normal_tcb[wp]:
  "\<And>t sender send_buf ep badge can_grant receiver recv_buf.
    \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_normal_transfer sender send_buf ep badge
                         can_grant receiver recv_buf
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

lemma valid_recv_ep_tcb:
  "\<lbrakk> valid_ep (RecvEP (a # lista)) s \<rbrakk> \<Longrightarrow> tcb_at a s"
  by (simp add: valid_ep_def tcb_at_def)


lemma copy_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>Q\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (c tcb) (tcb_arch tcb)\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
               "\<And>x. \<lbrace>Q\<rbrace> do_machine_op (loadWord x) \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>Q\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: copy_mrs_redux)
  apply (wp mapM_wp [where S=UNIV, simplified] dmo ts | wpc
       | simp add: store_word_offs_def load_word_offs_def
       | rule as_user_wp_thread_set_helper hoare_drop_imps)+
  done


lemma set_mrs_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     set_mrs a b c
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_refs_trivial | simp)+


lemma set_mrs_cur [wp]:
  "\<lbrace>cur_tcb\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  by (wp set_mrs_thread_set_dmo)

lemma set_mrs_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda> s. P (state_hyp_refs_of s)\<rbrace> set_mrs thread buf msgs \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_hyp_refs_trivial | simp)+

lemma set_mrs_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_iflive_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_ifunsafe_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_zombies_trivial
         ball_tcb_cap_casesI | simp)+


lemma set_mrs_valid_globals[wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_mrs a b c \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_global_refs_triv
         ball_tcb_cap_casesI valid_global_refs_cte_lift | simp)+


context Ipc_AI begin

crunch aligned[wp]: do_ipc_transfer "pspace_aligned :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch "distinct"[wp]: do_ipc_transfer "pspace_distinct :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps zipWithM_x_mapM)

crunch vmdb[wp]: set_message_info "valid_mdb :: 'state_ext state \<Rightarrow> bool"

crunch vmdb[wp]: do_ipc_transfer "valid_mdb :: 'state_ext state \<Rightarrow> bool"
  (ignore: as_user set_object simp: crunch_simps ball_conj_distrib
       wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_mdb)

crunch ifunsafe[wp]: do_ipc_transfer "if_unsafe_then_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch iflive[wp]: do_ipc_transfer "if_live_then_nonz_cap :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps sched_context_update_consumed_if_live simp: zipWithM_x_mapM gets_the_wp
   ignore: transfer_caps_loop set_object sched_context_update_consumed)

(* Move to Realtime_AI *)
lemma sched_context_update_consumed_if_live[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     sched_context_update_consumed param_a \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def
     simp_del: refs_of_defs fun_upd_apply
     wp: get_sched_context_wp get_object_wp)
  by (clarsimp simp: refs_of_def fun_upd_idem
       dest!: ko_at_state_refs_ofD simp del: refs_of_defs refs_of_simps)

crunch state_refs_of[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (state_refs_of s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop set_object)

crunch ct[wp]: do_ipc_transfer "cur_tcb :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop set_object)

crunch zombies[wp]: do_ipc_transfer "zombies_final :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift tcl_zombies simp: crunch_simps ball_conj_distrib )

crunch it[wp]: set_message_info "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: mapM_wp' set_message_info_it ignore: set_message_info)

crunch it[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (idle_thread s)"
  (wp: sched_context_update_consumed_it crunch_wps
    simp: crunch_simps zipWithM_x_mapM ignore: set_object)

crunch valid_globals[wp]: do_ipc_transfer "valid_global_refs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: crunch_simps zipWithM_x_mapM ball_conj_distrib
   ignore: set_object)

end

lemma set_mrs_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_mrs param_a param_b param_c \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (wp set_mrs_thread_set_dmo thread_set_valid_idle_trivial
         ball_tcb_cap_casesI | simp)+

context Ipc_AI begin

crunch valid_idle[wp]: do_ipc_transfer "valid_idle :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch arch[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (arch_state s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch typ_at[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (typ_at T p s)"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

crunch irq_node[wp]: do_ipc_transfer "\<lambda>s::'state_ext state. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

(* FIXME: move to KHeap_AI? *)
interpretation
  set_mrs: non_aobj_op "set_mrs t buf msg"
  unfolding set_mrs_def
  apply (unfold_locales)
  by (wpsimp wp: set_object_non_arch get_object_wp mapM_wp'
           simp: zipWithM_x_mapM non_arch_obj_def
         | rule conjI)+

lemma do_ipc_transfer_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>r s :: 'state_ext state. P (obj_at P' pd s)\<rbrace>"
  unfolding
    do_ipc_transfer_def do_normal_transfer_def set_message_info_def transfer_caps_def
    copy_mrs_def do_fault_transfer_def sched_context_update_consumed_def
  apply (wpsimp wp: as_user.aobj_at set_mrs.aobj_at hoare_drop_imps mapM_wp' transfer_caps_loop_aobj_at)
       apply (case_tac f, simp split del: if_split)
          by (wpsimp simp: sched_context_update_consumed_def
                 wp: as_user.aobj_at hoare_drop_imps set_sched_context.aobj_at)+

lemma do_ipc_transfer_valid_arch[wp]:
  "\<lbrace>valid_arch_state\<rbrace>
    do_ipc_transfer s ep bg grt r \<lbrace>\<lambda>rv. valid_arch_state :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  by (rule valid_arch_state_lift_aobj_at; wp do_ipc_transfer_aobj_at)

end

lemma set_mrs_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply ((wp valid_irq_handlers_lift thread_set_caps_of_state_trivial
              ball_tcb_cap_casesI | simp)+)[1]
  apply wp
  done

lemma copy_mrs_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> copy_mrs s sb r rb n \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (rule copy_mrs_thread_set_dmo)
   apply ((wp valid_irq_handlers_lift thread_set_caps_of_state_trivial
              ball_tcb_cap_casesI | simp)+)[1]
  apply wp+
  done


context Ipc_AI begin

crunch irq_handlers[wp]: do_ipc_transfer "valid_irq_handlers :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift simp: zipWithM_x_mapM crunch_simps ball_conj_distrib)

crunch valid_global_objs[wp]: do_ipc_transfer "valid_global_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: make_arch_fault_msg)

crunch vspace_objs[wp]: do_ipc_transfer "valid_vspace_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch valid_global_vspace_mappings[wp]: do_ipc_transfer "valid_global_vspace_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_valid_vspace_objs simp: zipWithM_x_mapM crunch_simps)

crunch arch_caps[wp]: do_ipc_transfer "valid_arch_caps :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift transfer_caps_loop_valid_arch_caps
   simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch v_ker_map[wp]: do_ipc_transfer "valid_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps)

crunch eq_ker_map[wp]: do_ipc_transfer "equal_kernel_mappings :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM crunch_simps ignore: set_object)

crunch asid_map [wp]: do_ipc_transfer "valid_asid_map :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

declare as_user_only_idle [wp]

crunch only_idle [wp]: store_word_offs only_idle

lemma set_mrs_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_mrs t b m \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_mrs_def split_def zipWithM_x_mapM
                   set_object_def
              cong: option.case_cong
               del: upt.simps)
  apply (wp mapM_wp'|wpc)+
  apply (clarsimp simp del: fun_upd_apply)
   apply (erule only_idle_tcb_update)
    apply (drule get_tcb_SomeD)
    apply (fastforce simp: obj_at_def)
   apply simp
  done

context Ipc_AI begin

crunch only_idle [wp]: do_ipc_transfer "only_idle :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_global_vspace_mappings [wp]: set_extra_badge valid_global_vspace_mappings

crunch pspace_in_kernel_window[wp]: do_ipc_transfer "pspace_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: crunch_simps)

end

lemma as_user_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> as_user t m \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (wp as_user_wp_thread_set_helper ball_tcb_cap_casesI
            thread_set_cap_refs_in_kernel_window
            | simp)+

lemma as_user_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> as_user t m \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (wp as_user_wp_thread_set_helper ball_tcb_cap_casesI
            thread_set_cap_refs_respects_device_region
            | simp)+

lemmas set_mrs_cap_refs_in_kernel_window[wp]
    = set_mrs_thread_set_dmo[OF thread_set_cap_refs_in_kernel_window
                                do_machine_op_cap_refs_in_kernel_window]


lemmas set_mrs_cap_refs_respects_device_region[wp]
    = set_mrs_thread_set_dmo[OF thread_set_cap_refs_respects_device_region
                                VSpace_AI.cap_refs_respects_device_region_dmo[OF storeWord_device_state_inv]]

context Ipc_AI begin

crunch cap_refs_in_kernel_window[wp]: do_ipc_transfer "cap_refs_in_kernel_window :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift ball_tcb_cap_casesI
     simp: zipWithM_x_mapM crunch_simps ball_conj_distrib)

lemma sched_context_update_consumed_valid_objs[wp]:
 "\<lbrace>valid_objs\<rbrace> sched_context_update_consumed scp \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (wpsimp simp: sched_context_update_consumed_def wp: get_sched_context_wp)
  by (drule valid_sched_context_objsI, simp add: obj_at_def)

crunch valid_objs[wp]: do_ipc_transfer "valid_objs :: 'state_ext state \<Rightarrow> bool"
  (wp: hoare_vcg_const_Ball_lift simp:ball_conj_distrib )

end

lemma as_user_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> as_user r f \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp: valid_ioc_def obj_at_def get_tcb_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

context Ipc_AI begin

lemma set_mrs_valid_ioc[wp]:
  "\<And>thread buf msgs.
    \<lbrace>valid_ioc :: 'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_mrs_def)
  apply (wp | wpc)+
     apply (simp only: zipWithM_x_mapM_x split_def)
     apply (wp mapM_x_wp[where S="UNIV", simplified] set_object_valid_ioc_caps static_imp_wp)+
    apply (rule hoare_strengthen_post, wp set_object_valid_ioc_caps, simp)
   apply wp
  apply (clarsimp simp: obj_at_def get_tcb_def valid_ioc_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (intro conjI impI allI)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                         cte_wp_at_cases null_filter_def)
   apply (simp add: tcb_cap_cases_def split: if_split_asm)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: cap_of_def tcb_cnode_map_tcb_cap_cases
                        cte_wp_at_cases null_filter_def)
  apply (simp add: tcb_cap_cases_def split: if_split_asm)
  done

crunch valid_ioc[wp]: do_ipc_transfer "valid_ioc :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_UNIV_wp)

end

lemma as_user_machine_state[wp]:
  "\<lbrace>\<lambda>s. P(machine_state s)\<rbrace> as_user r f \<lbrace>\<lambda>_. \<lambda>s. P(machine_state s)\<rbrace>"
  by (wp | simp add: as_user_def split_def)+

lemma set_mrs_def2:
  "set_mrs thread buf msgs \<equiv>
   do thread_set
        (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set
                     (\<lambda>reg. if reg \<in> set (take (length msgs) msg_registers)
                           then msgs ! the_index msg_registers reg
                           else (arch_tcb_context_get o tcb_arch) tcb reg) (tcb_arch tcb)\<rparr>)
        thread;
      remaining_msgs \<leftarrow> return (drop (length msg_registers) msgs);
      case buf of
      None \<Rightarrow> return $ nat_to_len (min (length msg_registers) (length msgs))
      | Some pptr \<Rightarrow>
          do zipWithM_x (store_word_offs pptr)
              [length msg_registers + 1..<Suc msg_max_length] remaining_msgs;
             return $ nat_to_len $ min (length msgs) msg_max_length
          od
   od"
  by (rule eq_reflection) (simp add: set_mrs_def thread_set_def bind_assoc)

context Ipc_AI begin

lemma set_mrs_vms[wp]:
  notes if_split [split del]
  shows "\<And>thread buf msgs.
    \<lbrace>valid_machine_state::'state_ext state \<Rightarrow> bool\<rbrace>
      set_mrs thread buf msgs
    \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  unfolding set_mrs_def2
  by (wpsimp simp: zipWithM_x_mapM_x split_def
               wp: mapM_x_wp_inv hoare_vcg_all_lift hoare_drop_imps)

crunch vms[wp]: do_ipc_transfer "valid_machine_state :: 'state_ext state \<Rightarrow> bool"
  (wp: mapM_UNIV_wp)

lemma do_ipc_transfer_invs[wp]:
  "\<lbrace>invs and tcb_at r and tcb_at s :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_ipc_transfer s ep bg grt r
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wpsimp simp: do_normal_transfer_def transfer_caps_def bind_assoc ball_conj_distrib
                  wp:  hoare_drop_imps get_rs_cte_at2 thread_get_wp
                       hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift)
  apply (clarsimp simp: obj_at_def is_tcb invs_valid_objs)
  done

lemma dit_tcb_at [wp]:
  "\<And>t s ep bg grt r.
    \<lbrace>tcb_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_ipc_transfer s ep bg grt r
    \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma dit_cte_at [wp]:
  "\<And>t s ep bg grt r.
    \<lbrace>cte_at t :: 'state_ext state \<Rightarrow> bool\<rbrace>
      do_ipc_transfer s ep bg grt r
    \<lbrace>\<lambda>rv. cte_at t\<rbrace>"
  by (wp valid_cte_at_typ)

end

lemma (in Ipc_AI) handle_fault_reply_typ_at[wp]:
  "\<lbrace>\<lambda>s :: 'state_ext state. P (typ_at T p s)\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by(cases ft, simp_all, wp+)

lemma (in Ipc_AI) handle_fault_reply_tcb[wp]:
  "\<lbrace>tcb_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace>
     handle_fault_reply ft t label msg
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma (in Ipc_AI) handle_fault_reply_cte[wp]:
  "\<lbrace>cte_at t' :: 'state_ext state \<Rightarrow> bool\<rbrace> handle_fault_reply ft t label msg \<lbrace>\<lambda>rv. cte_at t'\<rbrace>"
  by (wp valid_cte_at_typ)
(*
lemma valid_reply_caps_awaiting_reply:
  "\<lbrakk>valid_reply_caps s; kheap s t = Some (TCB tcb);
    has_reply_cap t s; tcb_state tcb = st\<rbrakk> \<Longrightarrow>
   awaiting_reply st"
  apply (simp add: valid_reply_caps_def pred_tcb_at_def)
  apply (fastforce simp: obj_at_def)
  done*)

lemmas cap_insert_typ_ats [wp] = abs_typ_at_lifts [OF cap_insert_typ_at]

context Ipc_AI begin

lemma do_ipc_transfer_non_null_cte_wp_at:
  fixes P ptr st ep b gr rt
  assumes imp: "\<And>c. P c \<Longrightarrow> \<not> is_untyped_cap c"
  shows
  "\<lbrace>valid_objs and cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr :: 'state_ext state \<Rightarrow> bool\<rbrace>
   do_ipc_transfer st ep b gr rt
   \<lbrace>\<lambda>_. cte_wp_at (P and (op \<noteq> cap.NullCap)) ptr\<rbrace>"
  unfolding do_ipc_transfer_def
  apply (wp do_normal_transfer_non_null_cte_wp_at hoare_drop_imp hoare_allI
    | wpc | simp add:imp)+
  done

end

lemma thread_get_tcb_at:
  "\<lbrace>\<top>\<rbrace> thread_get f tptr \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  unfolding thread_get_def
  by (wp, clarsimp simp add: get_tcb_ko_at tcb_at_def)


lemmas st_tcb_ex_cap' = st_tcb_ex_cap [OF _ invs_iflive]


lemma cap_delete_one_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (tcb_at p s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (tcb_at p s')\<rbrace>"
  by (clarsimp simp add: tcb_at_typ, rule cap_delete_one_typ_at)


lemma cap_delete_one_ep_at [wp]:
  "\<lbrace>\<lambda>s. P (ep_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (ep_at word s')\<rbrace>"
  by (simp add: ep_at_typ, wp)

lemma cap_delete_one_reply_at [wp]:
  "\<lbrace>\<lambda>s. P (reply_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (reply_at word s')\<rbrace>"
  by (simp add: reply_at_typ, wp)

lemma cap_delete_one_ntfn_at [wp]:
  "\<lbrace>\<lambda>s. P (ntfn_at word s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (ntfn_at word s')\<rbrace>"
  by (simp add: ntfn_at_typ, wp)

lemma cap_delete_one_valid_tcb_state:
  "\<lbrace>\<lambda>s. P (valid_tcb_state st s)\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s'. P (valid_tcb_state st s')\<rbrace>"
  apply (simp add: valid_tcb_state_def)
  apply (cases st, (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift cong: conj_cong split: option.splits)+)
       defer
       defer
       apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift cong: conj_cong split: option.splits)+
      defer
      apply (wpsimp wp: hoare_drop_imp hoare_vcg_all_lift cong: conj_cong split: option.splits)+
  sorry

lemma cte_wp_at_reply_cap_can_fast_finalise:
  "cte_wp_at (op = (cap.ReplyCap tcb)) slot s \<longrightarrow> cte_wp_at can_fast_finalise slot s"
  by (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)

context Ipc_AI begin

crunch st_tcb_at[wp]: do_ipc_transfer "st_tcb_at  P t :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps transfer_caps_loop_pres simp: zipWithM_x_mapM)

end

definition
  "queue_of ep \<equiv> case ep of
     Structures_A.IdleEP \<Rightarrow> []
   | Structures_A.SendEP q \<Rightarrow> q
   | Structures_A.RecvEP q \<Rightarrow> q"


primrec
  threads_of_ntfn :: "ntfn \<Rightarrow> obj_ref list"
where
  "threads_of_ntfn (ntfn.WaitingNtfn ts) = ts"
| "threads_of_ntfn (ntfn.IdleNtfn)       = []"
| "threads_of_ntfn (ntfn.ActiveNtfn x) = []"


primrec (nonexhaustive)
  threads_of :: "Structures_A.kernel_object \<Rightarrow> obj_ref list"
where
  "threads_of (Notification x) = threads_of_ntfn (ntfn_obj x)"
| "threads_of (TCB x)           = []"
| "threads_of (Endpoint x)      = queue_of x"


crunch ex_cap[wp]: set_message_info "ex_nonz_cap_to p"

(*
lemma tcb_bound_refs_eq_restr:
  "get_refs TCBBound mptr = {x. x \<in> id tcb_bound_refs mptr \<and> snd x = TCBBound}"
  by (auto dest: refs_in_tcb_bound_refs)
*)

crunches maybe_donate_sc
  for equal_kernel_mappings[wp]: equal_kernel_mappings
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and valid_arch_caps[wp]: valid_arch_caps
  and valid_arch_state[wp]: valid_arch_state
  and valid_asid_map[wp]: valid_asid_map
  and valid_global_objs[wp]: valid_global_objs
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and valid_vspace_objs[wp]: valid_vspace_objs
  and pspace_aligned[wp]: pspace_aligned
  and pspace_distinct[wp]: pspace_distinct
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and only_idle[wp]: only_idle
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and valid_global_refs[wp]: valid_global_refs
  and valid_ioc[wp]: valid_ioc
  and valid_irq_handlers[wp]: valid_irq_handlers
  and valid_irq_node[wp]: valid_irq_node
  and valid_irq_states[wp]: valid_irq_states
  and valid_machine_state[wp]: valid_machine_state
  and valid_mdb[wp]: valid_mdb
  and cte_wp_at[wp]: "cte_wp_at P c"
  and zombies_final[wp]: zombies_final
  (wp: maybeM_inv)

lemma gsc_ntfn_sp:
  "\<lbrace>P\<rbrace> get_ntfn_obj_ref ntfn_sc ntfnptr
   \<lbrace>\<lambda>sc s. (\<exists>ntfn. kheap s ntfnptr = Some (Notification ntfn) \<and> ntfn_sc ntfn = sc) \<and> P s\<rbrace>"
  apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply auto
  done

lemma maybe_donate_sc_if_live_then_nonz_cap[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> ex_nonz_cap_to tptr s
        \<and> (\<forall>scptr ntfn. kheap s ntfnptr = Some (Notification ntfn) \<and> ntfn_sc ntfn = Some scptr
                        \<longrightarrow> ex_nonz_cap_to scptr s)\<rbrace>
   maybe_donate_sc tptr ntfnptr
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def wp: maybeM_wp weak_if_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_valid_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> tptr \<noteq> idle_thread s\<rbrace> maybe_donate_sc tptr ntfnptr \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def get_sched_context_def get_object_def sc_tcb_sc_at_def
                       obj_at_def
                   wp: maybeM_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> maybe_donate_sc tptr ntfnptr \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt)
   apply clarsimp
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (wpsimp simp: get_sc_obj_ref_def pred_tcb_at_def obj_at_def is_tcb
                   wp: maybeM_wp weak_if_wp)
  apply wpsimp
  done

lemma maybe_donate_sc_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> maybe_donate_sc r n \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma maybe_donate_sc_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>r s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp simp: maybe_donate_sc_def sched_context_donate_def
               wp: hoare_vcg_if_lift2 hoare_drop_imp)

lemma sym_refs_helper_update_waiting_invs:
  "\<lbrace>\<lambda>s. sym_refs (\<lambda>a. if a = tptr then {r \<in> state_refs_of s tptr. snd r = TCBBound \<or>
                                        snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                      else state_refs_of s a)\<rbrace>
   maybe_donate_sc tptr ntfnptr
   \<lbrace>\<lambda>rv s. sym_refs (\<lambda>a. if a = tptr then {r \<in> state_refs_of s tptr. snd r = TCBBound \<or>
                                           snd r = TCBSchedContext \<or> snd r = TCBYieldTo}
                         else state_refs_of s a)\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; simp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (case_tac x)
    apply (clarsimp simp: maybeM_def)
    apply wpsimp
   apply (clarsimp simp: maybeM_def)
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (case_tac sc_tcb)
    apply (simp add: sched_context_donate_def)
    apply (rule hoare_seq_ext[OF _ gsct_sp])
    apply (case_tac from_opt)
     apply wpsimp
     apply (intro conjI)
      apply (fastforce simp: sc_tcb_sc_at_def obj_at_def pred_tcb_at_def)
     apply clarsimp
     apply (rule delta_sym_refs, assumption)
      apply (fastforce split: if_splits)
     apply (clarsimp split: if_splits)
      apply (frule pred_tcb_at_tcb_at)
      apply (fastforce simp: state_refs_of_def obj_at_def get_refs_def2 pred_tcb_at_def
                             tcb_st_refs_of_def
                      split: thread_state.splits if_splits)
     apply (clarsimp simp: sc_tcb_sc_at_def obj_at_def state_refs_of_def get_refs_def2)
    apply (wpsimp simp: sc_tcb_sc_at_def obj_at_def)
   apply wpsimp
  apply wpsimp
  done

lemma not_idle_tcb_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_idle s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> \<forall>t\<in>set q. t \<noteq> idle_thread s"
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = ntfnptr in allE)
  apply (erule_tac x = "(idle_thread s, NTFNSignal)" in ballE)
   apply (auto simp: state_refs_of_def valid_idle_def obj_at_def pred_tcb_at_def)
  done

lemma ex_nonz_cap_to_tcb_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_objs s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> if_live_then_nonz_cap s \<Longrightarrow> \<forall>t\<in>set q. ex_nonz_cap_to t s"
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule_tac x = t in ballE)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfnptr in allE)
   apply (erule_tac x = "(t, NTFNSignal)" in ballE)
    apply (auto simp: state_refs_of_def is_tcb get_refs_def2 live_def dest!: if_live_then_nonz_capD)
  done

lemma st_in_waitingntfn:
  "kheap s ntfnptr = Some (Notification ntfn) \<Longrightarrow> ntfn_obj ntfn = WaitingNtfn q \<Longrightarrow> valid_objs s
   \<Longrightarrow> sym_refs (state_refs_of s)
   \<Longrightarrow> \<forall>t\<in>set q. st_tcb_at (\<lambda>x. x = BlockedOnNotification ntfnptr) t s"
  apply (erule (1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (erule_tac x = t in ballE)
   apply (clarsimp simp: sym_refs_def)
   apply (erule_tac x = ntfnptr in allE)
   apply (erule_tac x = "(t, NTFNSignal)" in ballE)
    apply (auto simp: state_refs_of_def is_tcb obj_at_def pred_tcb_at_def tcb_st_refs_of_def
                      get_refs_def2
               split: thread_state.splits if_splits)
  done

lemma update_waiting_invs:
  notes if_split[split del] hoare_pre [wp_pre del]
  shows
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>ntfn. ko_at (Notification ntfn) ntfnptr s
        \<and> ntfn_obj ntfn = WaitingNtfn q \<and> ntfn_bound_tcb ntfn = bound_tcb \<and> ntfn_sc ntfn = sc)
        \<and> (bound sc \<longrightarrow> ex_nonz_cap_to (the sc) s)\<rbrace>
   update_waiting_ntfn ntfnptr q bound_tcb sc bdg
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: update_waiting_ntfn_def)
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: valid_irq_node_typ sts_only_idle)
   apply (wpsimp simp: valid_tcb_state_def conj_comms)
   apply (wpsimp simp: maybe_donate_sc_def
                   wp: hoare_vcg_conj_lift sym_refs_helper_update_waiting_invs)
  apply (simp add: invs_def valid_state_def valid_pspace_def obj_at_def)
  apply wpsimp
        apply (rule hoare_conjI)
         apply (wpsimp simp: set_simple_ko_def set_object_def get_object_def
                       split: option.splits)
         apply (fastforce simp: obj_at_def is_ntfn elim!: ex_cap_to_after_update)
        apply (wpsimp wp: valid_irq_node_typ)
                      defer
                      apply (clarsimp simp: not_idle_tcb_in_waitingntfn
                                            ex_nonz_cap_to_tcb_in_waitingntfn)+
       apply (fastforce simp: live_def live_ntfn_def elim!: if_live_then_nonz_capD2)
      apply (clarsimp simp: ex_nonz_cap_to_tcb_in_waitingntfn)
     apply clarsimp+
   apply (case_tac q; simp)
   apply (fastforce simp: valid_obj_def valid_ntfn_def
                   elim!: valid_objsE
                   split: option.splits list.splits)
  apply (rule valid_objsE, assumption+)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def)
  apply (subgoal_tac "st_tcb_at (\<lambda>x. x = BlockedOnNotification ntfnptr) (hd q) s")
   apply (case_tac q; simp)
   apply (rule delta_sym_refs, assumption)
    apply (fastforce simp: state_refs_of_def split: if_splits list.splits)
   apply (fastforce simp: state_refs_of_def get_refs_def2 st_tcb_at_def obj_at_def
                   split: if_splits list.splits)
  apply (clarsimp simp: st_in_waitingntfn)
  done


lemma cancel_ipc_ex_nonz_tcb_cap:
  "\<lbrace>\<lambda>s. \<exists>ptr. cte_wp_at (op = (cap.ThreadCap p)) ptr s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state
              del: split_paired_Ex)
  apply (wp cancel_ipc_caps_of_state)
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
   apply (rule_tac x="(a, b)" in exI)
   apply (clarsimp simp: cte_wp_at_caps_of_state can_fast_finalise_def)
  done


lemma valid_cap_tcb_at_tcb_or_zomb:
  "\<lbrakk> s \<turnstile> cap; t \<in> obj_refs cap; tcb_at t s \<rbrakk>
       \<Longrightarrow> is_thread_cap cap \<or> is_zombie cap"
  by (rule obj_ref_is_tcb)


lemma cancel_ipc_ex_nonz_cap_to_tcb:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s \<and> valid_objs s \<and> tcb_at p s\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (wp cancel_ipc_ex_nonz_tcb_cap)
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (frule(1) cte_wp_at_valid_objs_valid_cap, clarsimp)
  apply (drule valid_cap_tcb_at_tcb_or_zomb[where t=p])
    apply (simp add: zobj_refs_to_obj_refs)
   apply assumption
  apply (fastforce simp: is_cap_simps)
  done


lemma cancel_ipc_simple2:
  "\<lbrace>K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain, rule cancel_ipc_simple, simp_all)
  apply (clarsimp simp: st_tcb_def2)
  apply fastforce
  done

lemma cancel_ipc_cte_wp_at_not_reply_state:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>\<lambda>s. \<forall>r. st_tcb_at (op \<noteq> (BlockedOnReply r)) t s \<and> cte_wp_at P p s\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>r. cte_wp_at P p\<rbrace>"
  apply (simp add: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; wpsimp split: option.splits)
  done

crunch idle[wp]: cancel_ipc "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps select_wp simp: crunch_simps unless_def)

lemma maybe_donate_sc_sc_tcb_at [wp]:
  "\<lbrace>st_tcb_at P tcb_ptr'\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr \<lbrace>\<lambda>rv. st_tcb_at P tcb_ptr'\<rbrace>"
  by (wpsimp simp: maybe_donate_sc_def get_sc_obj_ref_def get_sk_obj_ref_def)

lemma maybe_donate_sc_not_idle_thread [wp]:
  "\<lbrace>\<lambda>s. tcb_ptr' \<noteq> idle_thread s\<rbrace>
   maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>rv s. tcb_ptr' \<noteq> idle_thread s\<rbrace>"
  by (wpsimp simp: maybe_donate_sc_def)

lemma maybe_donate_sc_sym_refs:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; simp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (case_tac x)
    apply (clarsimp simp: maybeM_def)
    apply wpsimp
   apply (clarsimp simp: maybeM_def)
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (case_tac sc_tcb)
    apply (simp add: sched_context_donate_def)
    apply (rule hoare_seq_ext[OF _ gsct_sp])
    apply (case_tac from_opt)
     apply wpsimp
     apply (fastforce simp: state_refs_of_def obj_at_def get_refs_def2 pred_tcb_at_def
                            sc_tcb_sc_at_def
                     elim!: delta_sym_refs
                     split: if_splits)
    apply (wpsimp simp: sc_tcb_sc_at_def obj_at_def)
   apply wpsimp
  apply wpsimp
  done

lemma maybe_donate_sc_invs [wp]:
  "\<lbrace>\<lambda>s. invs s \<and> ex_nonz_cap_to tcb_ptr s\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                  wp: maybe_donate_sc_sym_refs)
  apply safe
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def is_sc_obj_def)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (case_tac ko; simp)
   apply (clarsimp simp: live_def live_sc_def
                  dest!: sym_refs_ko_atD[unfolded obj_at_def, simplified])
  apply (clarsimp simp: idle_no_ex_cap)
  done

(* TODO: sts_invs_minor2 and sts_invs_minor2_concise: just preserve one version? *)
lemma sts_invs_minor2_concise:
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st \<and> \<not> awaiting_reply st') t
    and invs and ex_nonz_cap_to t and (\<lambda>s. t \<noteq> idle_thread s)
    and K (\<not> awaiting_reply st \<and> \<not>idle st)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle)
  apply clarsimp
  apply (rule conjI, simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def doubleton_eq_iff
                  split: thread_state.splits if_split_asm)
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: st_tcb_at_state_refs_ofD)
  apply (auto simp: get_refs_def split: option.splits)
  done

lemma sai_invs[wp]:
  "\<lbrace>invs and ex_nonz_cap_to ntfnptr\<rbrace> send_signal ntfnptr bdg \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: send_signal_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; simp)
    apply (case_tac "ntfn_bound_tcb ntfn"; simp)
     apply (wp set_ntfn_minor_invs)
     apply (fastforce simp: obj_at_def invs_def valid_pspace_def valid_state_def valid_obj_def
                            valid_ntfn_def)
    apply (rename_tac tptr)
    apply (rule hoare_seq_ext[OF _ gts_sp])
    apply (case_tac "receive_blocked st"; simp)
     apply (wpsimp wp: sts_invs_minor2_concise)
      apply (rule hoare_vcg_conj_lift)
       apply (rule hoare_strengthen_post)
        apply (wpsimp wp: cancel_ipc_invs_st_tcb_at)
       apply (fastforce simp: st_tcb_at_def obj_at_def)
      apply (wpsimp wp: cancel_ipc_ex_nonz_cap_to_tcb)
     apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
     apply (subgoal_tac "ex_nonz_cap_to tptr s")
      apply (fastforce simp: st_tcb_def2 is_tcb idle_no_ex_cap)
     apply (clarsimp simp: pred_tcb_at_def obj_at_def)
     apply (fastforce simp: live_def receive_blocked_def intro!: if_live_then_nonz_capD2)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
    apply (fastforce simp: valid_obj_def valid_ntfn_def state_refs_of_def obj_at_def
                    elim!: delta_sym_refs valid_objsE
                    split: if_splits)
   apply (wpsimp simp: obj_at_def invs_def valid_state_def valid_pspace_def
                   wp: update_waiting_invs)
   apply (erule (1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def sc_at_typ2 obj_at_def)
   apply (erule (1) if_live_then_nonz_capD2)
   apply (clarsimp simp: live_def live_sc_def
                  dest!: sym_refs_ko_atD[unfolded obj_at_def, simplified])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
  apply (fastforce simp: valid_obj_def valid_ntfn_def state_refs_of_def obj_at_def
                  elim!: delta_sym_refs
                  split: if_splits)
  done

crunch typ_at[wp]: send_signal "\<lambda>(s::det_ext state). P (typ_at T t s)"
(wp: hoare_drop_imps maybeM_inv)

lemma ncof_invs [wp]:
  "\<lbrace>invs\<rbrace> null_cap_on_failure (lookup_cap t ref) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: null_cap_on_failure_def | wp)+


lemma ncof_is_a_catch:
  "null_cap_on_failure m = (m <catch> (\<lambda>e. return Structures_A.NullCap))"
  apply (simp add: null_cap_on_failure_def liftM_def catch_def)
  apply (rule bind_cong [OF refl])
  apply (case_tac v, simp_all)
  done


lemma recv_ep_distinct:
  assumes inv: "invs s"
  assumes ep: "obj_at (\<lambda>k. k = Endpoint (Structures_A.endpoint.RecvEP
                                           q)) word1 s"
  shows "distinct q" using assms
  apply -
  apply (drule invs_valid_objs)
  apply (erule(1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_ep_def)
  done

lemma rfk_invs: "\<lbrace>invs and tcb_at t\<rbrace> reply_from_kernel t r \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding reply_from_kernel_def by (cases r; wpsimp)

lemma st_tcb_at_valid_st:
  "\<lbrakk> invs s ; tcb_at t s ; st_tcb_at (op= st) t s \<rbrakk> \<Longrightarrow> valid_tcb_state st s"
  apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
                  valid_objs_def tcb_at_def get_tcb_def pred_tcb_at_def
                  obj_at_def)
  apply (drule_tac x=t in bspec)
   apply (erule domI)
  apply (simp add: valid_obj_def valid_tcb_def)
  done




lemma gts_eq_ts:
  "\<lbrace> tcb_at thread \<rbrace> get_thread_state thread \<lbrace>\<lambda>rv. st_tcb_at (op= rv) thread \<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule gts_sp)
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def)
  done


declare lookup_cap_valid [wp]

context Ipc_AI begin

lemma send_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"

  sorry
(*
crunch typ_at[wp]: send_ipc "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)
*)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      send_ipc call bl w d cd t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma handle_fault_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault t f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: handle_fault_def unless_def handle_no_fault_def send_fault_ipc_def)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t tptr handler_cap fault can_donate.
    \<lbrace>tcb_at t :: det_ext state \<Rightarrow> bool\<rbrace>
      send_fault_ipc tptr handler_cap fault can_donate
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def)

end


definition
  "pspace_clear t s \<equiv> s \<lparr> kheap := (kheap s) (t := None) \<rparr>"


lemma pred_tcb_at_update1:
  "x \<noteq> t \<Longrightarrow> pred_tcb_at proj P x (s\<lparr>kheap := (kheap s)(t := v)\<rparr>) = pred_tcb_at proj P x s"
  by (simp add: pred_tcb_at_def obj_at_def)


lemma pred_tcb_at_update2:
  "pred_tcb_at proj P t (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = P (proj (tcb_to_itcb tcb))"
  by (simp add: pred_tcb_at_def obj_at_def)


lemma pred_tcb_clear:
  "pred_tcb_at proj P t (pspace_clear t' s) = (t \<noteq> t' \<and> pred_tcb_at proj P t s)"
  by (simp add: pred_tcb_at_def obj_at_def pspace_clear_def)


lemma pred_tcb_upd_apply:
  "pred_tcb_at proj P t (s\<lparr>kheap := kheap s(r \<mapsto> TCB v)\<rparr>) =
  (if t = r then P (proj (tcb_to_itcb v)) else pred_tcb_at proj P t s)"
  by (simp add: pred_tcb_at_def obj_at_def)


lemmas (in Ipc_AI) transfer_caps_loop_cap_to[wp]
  = transfer_caps_loop_pres [OF cap_insert_ex_cap]

crunch cap_to[wp]: set_extra_badge "ex_nonz_cap_to p"

context Ipc_AI begin
crunch cap_to[wp]: do_ipc_transfer "ex_nonz_cap_to p :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps simp: zipWithM_x_mapM ignore: transfer_caps_loop)

lemma receive_ipc_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>
   receive_ipc thread cap is_blocking reply_cap \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (simp add: receive_ipc_def)
  apply (case_tac cap; simp)
  apply (case_tac reply_cap; simp)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
   apply (rule hoare_seq_ext[OF _ gbn_sp])
   apply (case_tac ntfnptr; simp)
    apply (case_tac x; simp)
      apply (case_tac is_blocking; simp)
       apply wpsimp
      apply (wpsimp simp: do_nbrecv_failed_transfer_def)
     apply (rule hoare_seq_ext[OF _ assert_sp])
  sorry

(*
crunch it[wp]: receive_ipc "\<lambda>s::det_ext state. P (idle_thread s)"
  (wp: hoare_drop_imps simp: crunch_simps zipWithM_x_mapM)
*)
end

lemma schedule_tcb_Pmdb[wp]: "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

crunch Pmdb[wp]: set_thread_state "\<lambda>s. P (cdt s)"

crunch irq_handlers[wp]: set_simple_ko "valid_irq_handlers"
  (wp: crunch_wps)


lemma same_caps_tcb_upd_state[simp]:
 "same_caps (TCB (tcb \<lparr>tcb_state := BlockedOnReply r\<rparr>)) = same_caps (TCB tcb)"
 apply (rule ext)
 apply (simp add:tcb_cap_cases_def)
 done

lemma same_caps_simps[simp]:
 "same_caps (CNode sz cs)  = (\<lambda>val. val = CNode sz cs)"
 "same_caps (TCB tcb)      = (\<lambda>val. (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb)))"
 "same_caps (Endpoint ep)  = (\<lambda>val. is_ep val)"
 "same_caps (Notification ntfn) = (\<lambda>val. is_ntfn val)"
 "same_caps (Reply rply)  = (\<lambda>val. is_reply val)"
 "same_caps (SchedContext sc n)  = (\<lambda>val. \<exists>sc'. val = SchedContext sc' n)"
 "same_caps (ArchObj ao)   = (\<lambda>val. (\<exists>ao'. val = ArchObj ao'))"
 apply (rule ext)
 apply (case_tac val, (fastforce simp: is_obj_defs)+)+
 done

lemma tcb_at_cte_at_2:
  "tcb_at tcb s \<Longrightarrow> cte_at (tcb, tcb_cnode_index 2) s"
  by (auto simp: obj_at_def cte_at_cases is_tcb)

lemma tcb_at_cte_at_3:
  "tcb_at tcb s \<Longrightarrow> cte_at (tcb, tcb_cnode_index 3) s"
  by (auto simp: obj_at_def cte_at_cases is_tcb)


context Ipc_AI begin
crunch valid_irq_states[wp]: do_ipc_transfer "valid_irq_states :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps  simp: crunch_simps)

crunch cap_refs_in_kernel_window[wp]: do_ipc_transfer "cap_refs_in_kernel_window"
  (wp: crunch_wps hoare_vcg_const_Ball_lift ball_tcb_cap_casesI
     simp: zipWithM_x_mapM crunch_simps ball_conj_distrib )

crunch cap_refs_respects_device_region[wp]: do_fault_transfer "cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch cap_refs_respects_device_region[wp]: do_fault_transfer "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch cap_refs_respects_device_region[wp]: copy_mrs "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM ball_conj_distrib)

crunch cap_refs_respects_device_region[wp]: get_receive_slots "cap_refs_respects_device_region"
  (wp: crunch_wps hoare_vcg_const_Ball_lift
    VSpace_AI.cap_refs_respects_device_region_dmo ball_tcb_cap_casesI
    const_on_failure_wp simp: crunch_simps zipWithM_x_mapM )



lemma invs_respects_device_region:
  "invs s \<Longrightarrow> cap_refs_respects_device_region s \<and> pspace_respects_device_region s"
  by (clarsimp simp: invs_def valid_state_def)

end

locale Ipc_AI_cont = Ipc_AI state_ext_t some_t
  for state_ext_t :: "'state_ext::state_ext itself"  and some_t :: "'t itself"+
  assumes do_ipc_transfer_pspace_respects_device_region[wp]:
    "\<And> t ep bg grt r.
      \<lbrace>pspace_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_ipc_transfer t ep bg grt r
      \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  assumes do_ipc_transfer_cap_refs_respects_device_region[wp]:
    "\<And> t ep bg grt r.
      \<lbrace>cap_refs_respects_device_region and tcb_at t and  valid_objs and valid_mdb\<rbrace>
        do_ipc_transfer t ep bg grt r
      \<lbrace>\<lambda>rv. cap_refs_respects_device_region :: 'state_ext state \<Rightarrow> bool\<rbrace>"
  assumes do_ipc_transfer_state_hyp_refs_of[wp]:
   "\<lbrace>\<lambda>s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>
     do_ipc_transfer t ep bg grt r
      \<lbrace>\<lambda>_ s::'state_ext state. P (state_hyp_refs_of s)\<rbrace>"


lemma complete_signal_invs:
  "\<lbrace>invs and tcb_at tcb\<rbrace> complete_signal ntfnptr tcb \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: complete_signal_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj ntfn"; simp)
  apply (wpsimp simp: as_user_def set_object_def wp: set_ntfn_minor_invs)
  apply safe
    apply (clarsimp simp: obj_at_def is_tcb)
   apply (fastforce simp: invs_def valid_state_def valid_pspace_def valid_bound_obj_def
                          valid_obj_def valid_ntfn_def is_tcb obj_at_def is_sc_obj_def
                   elim!: valid_objsE
                   split: option.splits)
  apply (fastforce simp: invs_def valid_state_def valid_pspace_def live_def live_ntfn_def
                         tcb_cap_cases_def is_tcb obj_at_def
                 intro!: ex_cap_to_after_update
                  elim!: if_live_then_nonz_capD)
  done

crunch pspace_respects_device_region[wp]: as_user "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region pspace_respects_device_region_dmo)

context Ipc_AI_cont begin
lemma ri_invs':
  fixes Q t cap is_blocking reply
  notes if_split[split del]
  notes hyp_refs_of_simps[simp del]
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> complete_signal a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a (s::'a::state_ext state). \<lbrace>Q and valid_objs\<rbrace> do_extended_op (possible_switch_to a) \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes dit_Q[wp]: "\<And>a b c d e. \<lbrace>valid_mdb and valid_objs and Q\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes failed_transfer_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> do_nbrecv_failed_transfer a \<lbrace>\<lambda>_. Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>(invs::det_ext state \<Rightarrow> bool) and Q and st_tcb_at active t and ex_nonz_cap_to t
         and cte_wp_at (op = cap.NullCap) (t, tcb_cnode_index 3)
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)\<rbrace>
     receive_ipc t cap is_blocking reply \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (simp add: receive_ipc_def split_def)
  apply (cases cap, simp_all)
  apply (rename_tac ep badge rights)
(*  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext[OF _ gbn_sp])
  apply (rule hoare_seq_ext)
  (* set up precondition for old proof *)
   apply (rule_tac R="ko_at (Endpoint x) ep and ?pre" in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   apply (case_tac x)
    apply (wp | rule hoare_pre, wpc | simp)+
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (rule hoare_pre, wp valid_irq_node_typ)
      apply (simp add: valid_ep_def)
      apply (wp valid_irq_node_typ sts_only_idle sts_ep_at_inv[simplified ep_at_def2, simplified]
                failed_transfer_Q[simplified do_nbrecv_failed_transfer_def, simplified]
            | simp add: live_def do_nbrecv_failed_transfer_def)+
     apply (clarsimp simp: st_tcb_at_tcb_at valid_tcb_state_def invs_def valid_state_def valid_pspace_def)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI)
      apply (subgoal_tac "ep \<noteq> t")
       apply (drule obj_at_state_refs_ofD)
       apply (drule active_st_tcb_at_state_refs_ofD)
       apply (erule delta_sym_refs)
        apply (clarsimp split: if_split_asm)
       apply (clarsimp split: if_split_asm if_split)
       apply (fastforce dest!: symreftype_inverse'
                         simp: pred_tcb_at_def2 tcb_bound_refs_def2)
      apply (clarsimp simp: obj_at_def st_tcb_at_def)
     apply (simp add: obj_at_def is_ep_def)
     apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                      simp: st_tcb_def2)
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wp hoare_drop_imps valid_irq_node_typ hoare_post_imp[OF disjI1]
              sts_only_idle
         | simp add: valid_tcb_state_def cap_range_def
         | strengthen reply_cap_doesnt_exist_strg | wpc
         | (wp hoare_vcg_conj_lift | wp dxo_wp_weak | simp)+)+
    apply (clarsimp simp: st_tcb_at_tcb_at neq_Nil_conv)
    apply (frule(1) sym_refs_obj_atD)
    apply (frule(1) hyp_sym_refs_obj_atD)
    apply (frule ko_at_state_refs_ofD)
    apply (frule ko_at_state_hyp_refs_ofD)
    apply (erule(1) obj_at_valid_objsE)
    apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_tcb_at
                          valid_obj_def ep_redux_simps
                    cong: list.case_cong if_cong)
    apply (frule(1) st_tcb_ex_cap[where P="\<lambda>ts. \<exists>pl. ts = st pl" for st],
           clarsimp+)
    apply (clarsimp simp: valid_ep_def)
    apply (frule active_st_tcb_at_state_refs_ofD)
    apply (frule st_tcb_at_state_refs_ofD
                 [where P="\<lambda>ts. \<exists>pl. ts = st pl" for st])
    apply (subgoal_tac "y \<noteq> t \<and> y \<noteq> idle_thread s \<and> t \<noteq> idle_thread s \<and>
                        idle_thread s \<notin> set ys")
     apply (clarsimp simp: st_tcb_def2 is_ep_def
       conj_comms tcb_at_cte_at_2)
     apply (clarsimp simp: obj_at_def)
     apply (erule delta_sym_refs)
      apply (clarsimp split: if_split_asm)
     apply (clarsimp split: if_split_asm if_split) (* FIXME *)
       apply ((fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 is_tcb
                       dest!: symreftype_inverse')+)[3]
    apply (rule conjI)
     apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     split: if_split_asm)
     apply (simp add: set_eq_subset)

    apply (rule conjI, clarsimp dest!: idle_no_ex_cap)+
    apply (simp add: idle_not_queued')
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle 
              sts_ep_at_inv[simplified ep_at_def2, simplified]
              failed_transfer_Q[unfolded do_nbrecv_failed_transfer_def, simplified]
              | simp add: live_def valid_ep_def do_nbrecv_failed_transfer_def
              | wpc)+
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
   apply (rule conjI, fastforce simp: st_tcb_def2)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (frule(1) sym_refs_ko_atD)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_ep_def)
   apply (rule context_conjI)
    apply (rule notI, (drule(1) bspec)+, (drule obj_at_state_refs_ofD)+, clarsimp)
    apply (clarsimp simp: pred_tcb_at_def2 tcb_bound_refs_def2)
    apply (blast intro: reftype.simps)
   apply (rule conjI, erule delta_sym_refs)
     apply (clarsimp split: if_split_asm if_split)
     apply (rule conjI, rule impI)
      apply (clarsimp simp: pred_tcb_at_def2 obj_at_def)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                     dest!: symreftype_inverse')
    apply (clarsimp split: if_split_asm if_split)
    apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2
                    dest!: symreftype_inverse')
   apply (fastforce simp: obj_at_def is_ep pred_tcb_at_def2 dest!: idle_no_ex_cap valid_reply_capsD)
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp | wpc | clarsimp)+
  apply (clarsimp simp: pred_tcb_at_tcb_at)
  done*) sorry

lemmas ri_invs[wp]
  = ri_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

end

crunch ntfn_at[wp]: set_message_info "ntfn_at ntfn"

crunch typ_at[wp]: set_message_info "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch arch[wp]: set_message_info "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_message_info_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (rule valid_arch_state_lift_aobj_at; wp?)
  unfolding set_message_info_def
  apply (wp as_user.aobj_at)
  done

crunch caps[wp]: set_message_info "\<lambda>s. P (caps_of_state s)"

crunch irq_node[wp]: set_message_info "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

lemma set_message_info_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_message_info a b \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wp)

crunch irq_node[wp]: set_mrs "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch interrupt_states[wp]: set_message_info "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps )

crunch interrupt_states[wp]: set_mrs "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps wp: crunch_wps)

lemma tcb_cap_cases_tcb_context:
  "\<forall>(getF, v)\<in>ran tcb_cap_cases.
         getF (tcb_arch_update (arch_tcb_context_set F) tcb) = getF tcb"
  by (rule ball_tcb_cap_casesI, simp+)

crunch valid_arch_caps[wp]: set_message_info "valid_arch_caps"

lemma valid_bound_tcb_exst[iff]:
 "valid_bound_tcb t (trans_state f s) = valid_bound_tcb t s"
  by (auto simp: valid_bound_obj_def split:option.splits)

crunch bound_tcb[wp]: set_message_info, set_mrs "valid_bound_tcb t"
(wp: valid_bound_tcb_typ_at set_object_typ_at mapM_wp ignore: set_object
 simp: zipWithM_x_mapM)

context Ipc_AI begin

lemma rai_invs':
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace> Q\<rbrace> set_notification a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes smi_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_message_info a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes as_user_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> as_user a b \<lbrace>\<lambda>r::unit. Q\<rbrace>"
  assumes set_mrs_Q[wp]: "\<And>a b c. \<lbrace>Q\<rbrace> set_mrs a b c \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)
         and (\<lambda>s. \<exists>ntfnptr. is_ntfn_cap cap \<and> cap_ep_ptr cap = ntfnptr \<and>
                     obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = None
                                                          \<or> ntfn_bound_tcb ntfn = Some t)) ntfnptr s)\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (cases cap, simp_all)
  apply (rename_tac ntfn badge rights)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj x")
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (rule hoare_pre)
     apply (wp set_simple_ko_valid_objs valid_irq_node_typ sts_only_idle
              sts_ntfn_at_inv[simplified ntfn_at_def2, simplified] | wpc
          | simp add: live_def valid_ntfn_def do_nbrecv_failed_transfer_def)+
(*    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
    apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
    apply (rule conjI, clarsimp simp: obj_at_def split: option.splits)
    apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def
                                dest!: st_tcb_at_tcb_at
                                split: option.splits)
    apply (rule conjI)

     apply (subgoal_tac "t \<noteq> ntfn")
      apply (drule ko_at_state_refs_ofD)
      apply (drule active_st_tcb_at_state_refs_ofD)
      apply (erule delta_sym_refs)
       apply (clarsimp split: if_split_asm)
      apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: if_split_asm)
     apply (clarsimp simp: obj_at_def pred_tcb_at_def)
    apply (simp add: is_ntfn obj_at_def)
    apply (fastforce dest!: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                    simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (rule hoare_pre)
    apply (wpsimp wp: set_simple_ko_valid_objs hoare_vcg_const_Ball_lift sts_only_idle
              valid_irq_node_typ sts_ntfn_at_inv[simplified ntfn_at_def2, simplified]
               simp: live_def valid_ntfn_def do_nbrecv_failed_transfer_def)
   apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
   apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
   apply (rule obj_at_valid_objsE, assumption+)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def)
   apply (frule(1) sym_refs_ko_atD, simp)
   apply (frule ko_at_state_refs_ofD)
   apply (frule active_st_tcb_at_state_refs_ofD)
   apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
   apply (rule context_conjI, fastforce simp: pred_tcb_at_def obj_at_def tcb_bound_refs_def2
                                               state_refs_of_def)
   apply (subgoal_tac "ntfn_bound_tcb x = None")
    apply (rule conjI, clarsimp split: option.splits)
    apply (rule conjI, erule delta_sym_refs)
      apply (fastforce simp: pred_tcb_at_def2 obj_at_def symreftype_inverse'
                      split: if_split_asm)
     apply (fastforce simp: pred_tcb_at_def2 tcb_bound_refs_def2 split: if_split_asm)
    apply (simp add: obj_at_def is_ntfn idle_not_queued)
    apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                    elim!: pred_tcb_weakenE
                     simp: st_tcb_at_reply_cap_valid st_tcb_def2)
   apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def
                   elim: obj_at_valid_objsE
                  split: option.splits)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_simple_ko_valid_objs hoare_vcg_const_Ball_lift
             as_user_ntfn_at[simplified ntfn_at_def2, simplified]
             valid_irq_node_typ ball_tcb_cap_casesI static_imp_wp
             | simp add: valid_ntfn_def)+
  apply clarsimp
  apply (rule conjI, clarsimp simp: valid_bound_tcb_def obj_at_def pred_tcb_at_def2 is_tcb
                             split: option.splits)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (rule conjI, erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp split: if_split_asm)
  apply (fastforce simp: obj_at_def is_ntfn_def state_refs_of_def
                        valid_idle_def pred_tcb_at_def
                        st_tcb_at_reply_cap_valid
                  dest: valid_reply_capsD)
  done *) sorry

lemmas rai_invs[wp] = rai_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

end

lemma pspace_clear_update1:
  "t \<noteq> t' \<Longrightarrow>
  pspace_clear t' (s\<lparr>kheap := (kheap s)(t := v)\<rparr>) =
  (pspace_clear t' s) \<lparr>kheap := (kheap (pspace_clear t' s))(t := v)\<rparr>"
  apply (simp add: pspace_clear_def)
  apply (cases s)
  apply simp
  apply (simp add: fun_upd_twist)
  done


lemma pspace_clear_update2:
  "pspace_clear t' (s\<lparr>kheap := (kheap s)(t' := v)\<rparr>) = pspace_clear t' s"
  by (simp add: pspace_clear_def)


lemmas pspace_clear_update = pspace_clear_update1 pspace_clear_update2


lemma clear_revokable [iff]:
  "pspace_clear t (is_original_cap_update f s) = is_original_cap_update f (pspace_clear t s)"
  by (simp add: pspace_clear_def)


context Ipc_AI begin
(*crunch cap_to[wp]: receive_ipc "ex_nonz_cap_to p :: det_ext state \<Rightarrow> bool"
  (wp: cap_insert_ex_cap hoare_drop_imps maybeM_inv simp: crunch_simps ignore: set_object)
*)
lemma receive_ipc_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> receive_ipc param_a param_b param_c param_d  \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  sorry
end

lemma maybe_return_sc_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def set_tcb_obj_ref_def set_object_def get_tcb_obj_ref_def
                      thread_get_def get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply (auto simp: tcb_cap_cases_def intro!: ex_cap_to_after_update)
  done

lemma schedule_tcb_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)


lemma receive_ipc_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> receive_ipc param_a param_b param_c param_d  \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  sorry

crunch cap_to[wp]: receive_signal "ex_nonz_cap_to p:: det_ext state \<Rightarrow> bool"
  (wp: crunch_wps maybeM_inv ignore: set_object set_tcb_obj_ref)


crunch ex_nonz_cap_to[wp]: set_message_info "ex_nonz_cap_to p"


lemma is_derived_not_Null [simp]:
  "\<not>is_derived m p c NullCap"
  by (auto simp add: is_derived_def cap_master_cap_simps dest: cap_master_cap_eqDs)

crunch mdb[wp]: set_message_info valid_mdb
  (wp: select_wp crunch_wps mapM_wp')

lemma ep_queue_cap_to:
  "\<lbrakk> ko_at (Endpoint ep) p s; invs s;
     \<lbrakk> live (Endpoint ep) \<longrightarrow> queue_of ep \<noteq> [] \<rbrakk>
        \<Longrightarrow> t \<in> set (queue_of ep) \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  apply (frule sym_refs_ko_atD, fastforce)
  apply (erule obj_at_valid_objsE, fastforce)
  apply (clarsimp simp: valid_obj_def)
  apply (cases ep, simp_all add: queue_of_def valid_ep_def live_def
                                 st_tcb_at_refs_of_rev)
   apply (drule(1) bspec)
   apply (erule st_tcb_ex_cap, clarsimp+)
  apply (drule(1) bspec)
  apply (erule st_tcb_ex_cap, clarsimp+)
  done

context Ipc_AI_cont begin

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> do_extended_op (possible_switch_to a) \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to ep and ex_nonz_cap_to t\<rbrace>
     send_ipc bl call ba cg can_donate t ep
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (case_tac epa, simp_all)
    apply (cases bl, simp_all)[1]
     apply (simp add: invs_def valid_state_def valid_pspace_def)
     apply (wpsimp wp: valid_irq_node_typ)
     apply (simp add: live_def valid_ep_def)
     apply (wp valid_irq_node_typ sts_only_idle sts_ep_at_inv[simplified ep_at_def2, simplified])
     apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
     apply (rule conjI, clarsimp elim!: obj_at_weakenE simp: is_ep_def)
     apply (rule conjI, subgoal_tac "t \<noteq> ep")
       apply (drule ko_at_state_refs_ofD active_st_tcb_at_state_refs_ofD)+
(*       apply (erule delta_sym_refs)
        apply (clarsimp split: if_split_asm)
       apply (fastforce simp: pred_tcb_at_def2
                       dest!: refs_in_tcb_bound_refs
                       split: if_split_asm)
      apply (clarsimp simp: pred_tcb_at_def obj_at_def)
     apply (simp add: obj_at_def is_ep)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
    apply wpsimp
   apply (rename_tac list)
   apply (cases bl, simp_all)[1]
    apply (simp add: invs_def valid_state_def valid_pspace_def)
    apply (wpsimp wp: valid_irq_node_typ)
    apply (simp add: live_def valid_ep_def)
    apply (wp hoare_vcg_const_Ball_lift valid_irq_node_typ sts_only_idle
              sts_ep_at_inv[simplified ep_at_def2, simplified])
    apply (clarsimp simp: valid_tcb_state_def st_tcb_at_tcb_at)
    apply (frule ko_at_state_refs_ofD)
    apply (frule active_st_tcb_at_state_refs_ofD)
    apply (subgoal_tac "t \<noteq> ep \<and> t \<notin> set list")
     apply (erule obj_at_valid_objsE, clarsimp+)
     apply (clarsimp simp: valid_obj_def valid_ep_def)
     apply (rule conjI, clarsimp simp: obj_at_def is_ep_def)
     apply (rule conjI, clarsimp simp: st_tcb_at_reply_cap_valid)
     apply (rule conjI, erule delta_sym_refs)
       apply (fastforce split: if_split_asm)
      apply (fastforce simp: pred_tcb_at_def2
                      dest!: refs_in_tcb_bound_refs
                      split: if_split_asm)
     apply (simp add: obj_at_def is_ep idle_not_queued)
     apply (fastforce dest: idle_no_ex_cap valid_reply_capsD
                     simp: st_tcb_def2)
    apply (rule conjI, clarsimp simp: pred_tcb_at_def obj_at_def)
    apply (drule(1) sym_refs_ko_atD, clarsimp simp: st_tcb_at_refs_of_rev)
    apply (drule(1) bspec, clarsimp simp: pred_tcb_at_def obj_at_def)
   apply wpsimp
  apply (rename_tac list)
  apply (case_tac list, simp_all add: invs_def valid_state_def valid_pspace_def split del:if_split)
  apply (wp valid_irq_node_typ)
          apply (simp add: if_apply_def2 )
          apply (wp sts_only_idle sts_st_tcb_at_cases valid_irq_node_typ)
          apply (wp hoare_drop_imps sts_st_tcb_at_cases valid_irq_node_typ do_ipc_transfer_tcb_caps
                    sts_only_idle hoare_vcg_if_lift hoare_vcg_disj_lift thread_get_wp' hoare_vcg_all_lift
               | clarsimp simp:is_cap_simps | wpc
               | strengthen reply_cap_doesnt_exist_strg
                            disjI2_strg[where Q="cte_wp_at (\<lambda>cp. is_master_reply_cap cp \<and> R cp) p s"]
               | (wp hoare_vcg_conj_lift static_imp_wp | wp dxo_wp_weak | simp)+)+
  apply (clarsimp simp: ep_redux_simps conj_ac cong: list.case_cong if_cong)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp simp: st_tcb_at_refs_of_rev st_tcb_at_tcb_at ep_at_def2)
  apply (frule ko_at_state_refs_ofD)
  apply (frule active_st_tcb_at_state_refs_ofD)
  apply (erule(1) obj_at_valid_objsE)
  apply clarsimp
  apply (subgoal_tac "distinct ([t, a, ep, idle_thread s])")
   apply (clarsimp simp: fun_upd_def[symmetric] fun_upd_idem)
   apply (clarsimp simp: valid_obj_def valid_ep_def neq_Nil_conv)
   apply (rule conjI, erule(1) st_tcb_ex_cap)
    apply clarsimp
   apply (simp add: obj_at_def is_ep idle_not_queued')
   apply (subgoal_tac "state_refs_of s t = {r \<in> state_refs_of s t. snd r = TCBBound}")
    apply (subst fun_upd_idem[where x=t], force simp: conj_commute)
    apply (subgoal_tac "sym_refs ((state_refs_of s)(ep := set lista \<times> {EPRecv}, a := {r \<in> state_refs_of s a. snd r = TCBBound}))")
     apply (fastforce elim!: pred_tcb_weakenE st_tcb_at_reply_cap_valid simp: conj_commute simp del: ntfn_at_def2)

    apply (erule delta_sym_refs)
     apply (clarsimp simp: fun_upd_def split: if_split_asm)
    apply (fastforce simp: fun_upd_def
                    dest!: symreftype_inverse' st_tcb_at_state_refs_ofD refs_in_tcb_bound_refs
                    split: if_split_asm)
   apply (clarsimp dest!: st_tcb_at_state_refs_ofD simp: sts_refs_of_helper)
   apply fastforce
  apply (drule bound_tcb_at_state_refs_ofD)
  apply (clarsimp simp: tcb_bound_refs_def2)
  apply (rule conjI, clarsimp dest!: st_tcb_at_state_refs_ofD, (auto simp: set_eq_iff)[1])
  apply (rule conjI, clarsimp, (auto simp: set_eq_iff)[1])
  apply (rule conjI, clarsimp simp: idle_no_ex_cap idle_not_queued' idle_only_sc_refs)
  apply (rule conjI, clarsimp dest!: st_tcb_at_tcb_at simp: obj_at_def is_tcb)
  apply (auto dest!: st_tcb_at_state_refs_ofD simp: idle_no_ex_cap idle_not_queued' idle_no_refs)
  done*) sorry

lemma hf_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> do_extended_op (possible_switch_to a) \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  including no_pre
  apply (simp add: handle_fault_def)
  apply wp
    apply (simp add: handle_no_fault_def)
(*    apply (wp sts_invs_minor)
   apply (simp add: send_fault_ipc_def Let_def)
   apply wp
     apply (rule_tac P="invs and Q and st_tcb_at active t and ex_nonz_cap_to t and
                        (\<lambda>_. valid_fault f) and (\<lambda>s. t \<noteq> idle_thread s) and
                        (\<lambda>s. \<forall>r \<in> zobj_refs handler_cap. ex_nonz_cap_to r s)"
                   in hoare_trivE)
     apply (case_tac handler_cap)
               apply (strengthen reply_cap_doesnt_exist_strg
            | clarsimp simp: tcb_cap_cases_def
            | rule conjI
            | wp hoare_drop_imps
                 thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                 thread_set_cte_wp_at_trivial
            | fastforce elim!: pred_tcb_weakenE
                       simp: invs_def valid_state_def valid_idle_def st_tcb_def2
                    split: Structures_A.thread_state.splits)+
              apply (rule hoare_pre_imp[rotated])
               apply (rule_tac P="valid_fault f" in hoare_gen_asm)
               apply (wp thread_set_invs_trivial)
                     apply (strengthen reply_cap_doesnt_exist_strg
             | clarsimp simp: tcb_cap_cases_def
             | rule conjI
             | wp hoare_drop_imps
                  thread_set_no_change_tcb_state ex_nonz_cap_to_pres
                  thread_set_cte_wp_at_trivial
             | fastforce elim!: pred_tcb_weakenE
                        simp: invs_def valid_state_def valid_idle_def pred_tcb_def2
                              valid_pspace_def idle_no_ex_cap
                     split: Structures_A.thread_state.splits)+
  done*) sorry


lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]

end

crunch pred_tcb_at[wp]: set_message_info "pred_tcb_at proj P t"

lemma reschedule_required_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> reschedule_required \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (wpsimp simp: reschedule_required_def set_scheduler_action_def tcb_sched_action_def
                   set_tcb_queue_def get_tcb_queue_def)

lemma schedule_tcb_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t'\<rbrace> schedule_tcb t \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  by (wpsimp simp: schedule_tcb_def wp: reschedule_required_pred_tcb_at)

lemma maybe_return_sc_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P tcb_ptr' and K (tcb_ptr \<noteq> tcb_ptr')\<rbrace> maybe_return_sc ntfn_ptr tcb_ptr
   \<lbrace>\<lambda>rv. pred_tcb_at proj P tcb_ptr'\<rbrace>"
  apply (wpsimp simp: maybe_return_sc_def set_sc_obj_ref_def set_tcb_obj_ref_def set_object_def
                      get_tcb_obj_ref_def thread_get_def get_sk_obj_ref_def get_simple_ko_def
                      get_object_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma maybe_donate_sc_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P tcb_ptr' and K (tcb_ptr \<noteq> tcb_ptr')\<rbrace> maybe_donate_sc tcb_ptr ntfn_ptr
   \<lbrace>\<lambda>rv. pred_tcb_at proj P tcb_ptr'\<rbrace>"
  apply (simp add: maybe_donate_sc_def)
  apply (rule hoare_seq_ext[OF _ gsc_sp])
  apply (case_tac sc_opt; simp)
   apply (rule hoare_seq_ext[OF _ gsc_ntfn_sp])
   apply (simp add: maybeM_def)
   apply (case_tac x; simp)
    apply wpsimp
   apply (rule hoare_seq_ext[OF _ gsct_sp])
   apply (case_tac sc_tcb; simp)
    apply (wpsimp simp: sched_context_donate_def set_tcb_obj_ref_def set_object_def
                        set_sc_obj_ref_def update_sched_context_def get_object_def get_tcb_def
                        pred_tcb_at_def obj_at_def get_sc_obj_ref_def get_sched_context_def)
    apply (fastforce simp: sc_tcb_sc_at_def obj_at_def)
   apply wpsimp
  apply wpsimp
  done

lemma sort_queue_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> sort_queue q \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (wpsimp simp: sort_queue_def wp: mapM_wp_inv)

lemma rai_pred_tcb_neq:
  "\<lbrace>pred_tcb_at proj P t' and K (t \<noteq> t')\<rbrace> receive_signal t cap is_blocking
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t'\<rbrace>"
  apply (simp add: receive_signal_def)
  apply (case_tac cap; simp)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (case_tac "ntfn_obj x"; simp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp wp: schedule_tcb_pred_tcb_at maybe_return_sc_pred_tcb_at sts_st_tcb_at_neq)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def)
   apply (case_tac is_blocking; simp)
    apply (wpsimp wp: schedule_tcb_pred_tcb_at maybe_return_sc_pred_tcb_at sort_queue_pred_tcb_at
                      sts_st_tcb_at_neq)
   apply (wpsimp simp: do_nbrecv_failed_transfer_def)
  apply (wpsimp wp: maybe_donate_sc_pred_tcb_at)
  done

context Ipc_AI begin
crunch ct[wp]: set_mrs "\<lambda>s::'state_ext state. P (cur_thread s)"
  (wp: case_option_wp mapM_wp)
end

context Ipc_AI begin

lemma receive_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> receive_ipc param_a param_b param_c param_d \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  sorry
(*
crunch typ_at[wp]: receive_ipc "\<lambda>s::det_ext state. P (typ_at T p s)"
  (wp: hoare_drop_imps maybeM_inv simp: crunch_simps)
*)
lemma ri_tcb [wp]:
  "\<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
    receive_ipc t cap is_blocking r
   \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

end

crunch typ_at[wp]: receive_signal "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)


lemma rai_tcb [wp]:
  "\<lbrace>tcb_at t'\<rbrace> receive_signal t cap is_blocking \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

context Ipc_AI begin

lemmas transfer_caps_loop_pred_tcb_at[wp] =
    transfer_caps_loop_pres [OF cap_insert_pred_tcb_at]

end


context Ipc_AI begin

lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
     send_ipc True call bdg x can_donate t' ep
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_inv])
  apply (case_tac epa, simp_all)
    apply (wp sts_st_tcb_at_cases)
    apply clarsimp
   apply (wp sts_st_tcb_at_cases)
   apply clarsimp
  apply (rule hoare_gen_asm[simplified])
  apply (rename_tac list)
  apply (case_tac list, simp_all split del:if_split)
(*  apply (rule hoare_seq_ext [OF _ set_simple_ko_pred_tcb_at])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac recv_state, simp_all split del: if_split)
  apply (wp sts_st_tcb_at_cases setup_caller_cap_makes_simple
            hoare_drop_imps
            | simp add: if_apply_def2 split del: if_split)+
  done *) sorry

end

lemma ep_ntfn_cap_case_helper:
  "(case x of cap.EndpointCap ref bdg r \<Rightarrow> P ref bdg r
           |  cap.NotificationCap ref bdg r \<Rightarrow> Q ref bdg r
           |  _ \<Rightarrow> R)
   = (if is_ep_cap x then P (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      if is_ntfn_cap x then Q (cap_ep_ptr x) (cap_ep_badge x) (cap_rights x) else
      R)"
  by (cases x, simp_all)

context Ipc_AI begin

lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
     send_fault_ipc t' handler_cap ft can_donate
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: send_fault_ipc_def Let_def ep_ntfn_cap_case_helper
             cong: if_cong)
  apply (wp si_blk_makes_simple hoare_drop_imps
            thread_set_no_change_tcb_state
       | simp)+
  sorry

lemma hf_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
     handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  unfolding handle_fault_def
sorry (*  by (wpsimp wp: sfi_makes_simple sts_st_tcb_at_cases hoare_drop_imps simp: handle_no_fault_def)*)

end

crunch pred_tcb_at[wp]: complete_signal "pred_tcb_at proj t p"

context Ipc_AI begin

lemma ri_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
     receive_ipc t cap is_blocking r
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  apply (rule hoare_gen_asm)
  apply (simp add: receive_ipc_def split_def)
  apply (case_tac cap, simp_all)
(*  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_seq_ext [OF _ gbn_sp])
  apply (rule hoare_seq_ext)
   apply (rename_tac ep I DO x CARE NOT)
   apply (rule_tac R="ko_at (Endpoint x) ep and ?pre" in hoare_vcg_if_split)
    apply (wp complete_signal_invs)
   apply (case_tac x, simp_all)
     apply (rule hoare_pre, wpc)
       apply (wp sts_st_tcb_at_cases, simp)
      apply (simp add: do_nbrecv_failed_transfer_def, wp)
     apply clarsimp
    apply (rule hoare_seq_ext [OF _ assert_sp])
    apply (rule hoare_seq_ext [where B="\<lambda>s. st_tcb_at simple t'"])
     apply (rule hoare_seq_ext [OF _ gts_sp])
     apply (rule hoare_pre)
      apply (wp setup_caller_cap_makes_simple sts_st_tcb_at_cases
                hoare_vcg_all_lift hoare_vcg_const_imp_lift
                hoare_drop_imps
           | wpc | simp)+
     apply (fastforce simp: pred_tcb_at_def obj_at_def)
    apply (wp, simp)
   apply (wp sts_st_tcb_at_cases | rule hoare_pre, wpc | simp add: do_nbrecv_failed_transfer_def)+
   apply (wp get_simple_ko_wp | wpc | simp)+
  done*) sorry

end

lemma rai_makes_simple:
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t')\<rbrace>
     receive_signal t cap is_blocking
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
   by (rule rai_pred_tcb_neq)


lemma thread_set_Pmdb:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  unfolding thread_set_def by wpsimp

end
