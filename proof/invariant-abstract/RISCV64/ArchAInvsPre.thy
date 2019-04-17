(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchAInvsPre
imports "../AInvsPre"
begin

context Arch begin

global_naming RISCV64

definition
  "kernel_mappings \<equiv> {x. x \<ge> pptr_base}"

lemma kernel_mappings_slots_eq: (* FIXME RISCV: check if needed *)
  "canonical_address p \<Longrightarrow> p \<in> kernel_mappings \<longleftrightarrow> ucast (p >> pt_bits_left max_pt_level) \<in> kernel_mapping_slots"
  apply (simp add: kernel_mappings_def kernel_mapping_slots_def word_le_nat_alt
                   ucast_mask_drop)
  sorry (*
  apply (fold word_le_nat_alt)
  apply (rule iffI)
   apply (simp add: bit_simps pptr_base_def pptrBase_def)
   apply (word_bitwise, simp)
  apply (simp add: pptr_base_def pptrBase_def bit_simps canonical_address_range mask_def)
  apply word_bitwise
  apply simp
  done *)

lemma ucast_ucast_mask9: "(ucast (x && mask asid_low_bits) :: asid_low_index) = ucast x"
  by (rule ucast_mask_drop, simp add: asid_low_bits_def)

lemma some_get_page_info_kmapsD:
  "\<lbrakk>get_page_info (aobjs_of s) pt_ref p = Some (b, a, attr, r);
    p \<in> kernel_mappings; canonical_address p; valid_global_vspace_mappings s; equal_kernel_mappings s\<rbrakk>
   \<Longrightarrow> (\<exists>sz. pageBitsForSize sz = a) \<and> r = {}"
  sorry (* FIXME RISCV
   apply (clarsimp simp: get_pdpt_info_def get_pml4_entry_def get_arch_obj_def
                         kernel_mappings_slots_eq get_page_info_def get_pdpt_entry_def get_pd_info_def
                         get_pd_entry_def get_pt_info_def get_pt_entry_def
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (erule valid_global_pml4_mappingsE)
   apply (clarsimp simp: equal_kernel_mappings_def obj_at_def)
   apply (drule_tac x=pd_ref in spec,
          drule_tac x="riscv_global_pt (arch_state s)" in spec, simp)
   apply (drule bspec, assumption)
   apply (clarsimp simp: valid_pml4_kernel_mappings_def pml4e_mapping_bits_def)
   apply (drule_tac x="ucast (p >> pml4_shift_bits)" in spec)
   apply (clarsimp simp: get_page_info_def get_pml4_entry_def get_arch_obj_def
                         get_pdpt_info_def get_pdpt_entry_def get_pd_info_def get_pd_entry_def
                         get_pt_info_def get_pt_entry_def bit_simps
                         kernel_mappings_slots_eq
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits
                         pml4e.splits pdpte.splits pde.splits pte.splits)
      apply (rule conjI, rule_tac x=X64SmallPage in exI, simp add: bit_simps)
      apply (simp add: valid_pml4e_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 30))" in spec)
      apply (clarsimp simp: valid_pdpte_kernel_mappings_def)
      apply (simp add: valid_pd_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 21))" in spec)
      apply (clarsimp simp: valid_pde_kernel_mappings_def)
      apply (simp add: valid_pt_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 12))" in spec)
      apply (clarsimp simp: valid_pte_kernel_mappings_def)
      apply (rule conjI, rule_tac x=X64LargePage in exI, simp add: bit_simps)
      apply (simp add: valid_pml4e_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 30))" in spec)
      apply (clarsimp simp: valid_pdpte_kernel_mappings_def)
      apply (simp add: valid_pd_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 21))" in spec)
      apply (clarsimp simp: valid_pde_kernel_mappings_def)
      apply (simp add: valid_pt_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (rule conjI, rule_tac x=X64HugePage in exI, simp add: bit_simps)
      apply (simp add: valid_pml4e_kernel_mappings_def obj_at_def ucast_ucast_mask9
                       valid_pdpt_kernel_mappings_def bit_simps pml4e_mapping_bits_def
                 split: pml4e.splits)
      apply (drule_tac x="ucast ((p >> 30))" in spec)
      apply (clarsimp simp: valid_pdpte_kernel_mappings_def)
   done *)

lemma get_page_info_gpd_kmaps:
  "\<lbrakk>valid_global_objs s; valid_arch_state s; canonical_address p;
    get_page_info (aobjs_of s) (riscv_global_pt (arch_state s)) p = Some (b, a, attr, r)\<rbrakk>
   \<Longrightarrow> p \<in> kernel_mappings"
  sorry (* FIXME RISCV
  apply (clarsimp simp: valid_global_objs_def valid_arch_state_def
                        obj_at_def
                        empty_table_def kernel_mappings_slots_eq)
  apply (drule_tac x="ucast (p >> pml4_shift_bits)" in spec; clarsimp)
  apply (rule ccontr)
  apply (clarsimp simp: get_page_info_def get_pml4_entry_def get_arch_obj_def
                        bit_simps ucast_ucast_mask9
                 split: option.splits pml4e.splits arch_kernel_obj.splits)
  done *)

lemma get_vspace_of_thread_reachable:
  "get_vspace_of_thread (kheap s) (arch_state s) t \<noteq> riscv_global_pt (arch_state s)
   \<Longrightarrow> \<exists>level. (\<exists>\<rhd> (level, get_vspace_of_thread (kheap s) (arch_state s) t)) s"
  sorry (* FIXME RISCV: adjust def of get_vspace_of_thread first
  by (auto simp: get_vspace_of_thread_vs_lookup
          split: Structures_A.kernel_object.splits if_split_asm option.splits
                 cap.splits arch_cap.splits) *)

lemma is_aligned_ptrFromPAddrD:
  "\<lbrakk>is_aligned (ptrFromPAddr b) a; a \<le> 30\<rbrakk> \<Longrightarrow> is_aligned b a"
  apply (clarsimp simp:ptrFromPAddr_def pptrBase_def baseOffset_def pAddr_base_def canonical_bit_def)
  apply (erule is_aligned_addD2)
  apply (rule is_aligned_weaken[where x = 30])
   apply (simp add:is_aligned_def)
  apply simp
  done

lemma some_get_page_info_umapsD:
  "\<lbrakk>get_page_info (aobjs_of s) pt_ref p = Some (b, a, attr, r);
    \<exists>\<rhd> (level, pt_ref) s; p \<notin> kernel_mappings; valid_vspace_objs s; pspace_aligned s;
    canonical_address p;
    valid_asid_table s; valid_objs s\<rbrakk>
   \<Longrightarrow> \<exists>sz. pageBitsForSize sz = a \<and> is_aligned b a \<and> data_at sz (ptrFromPAddr b) s"
  sorry (* FIXME RISCV
  apply (clarsimp simp: get_page_info_def  get_pd_info_def get_pt_info_def
                        get_pml4_entry_def get_pdpt_entry_def get_pd_entry_def get_pt_entry_def
                        get_arch_obj_def valid_asid_table_def bit_simps
                        kernel_mappings_slots_eq
                 split: option.splits kernel_object.splits arch_kernel_obj.splits
                        pml4e.splits pdpte.splits pde.splits pte.splits)
    apply (all \<open>drule (2) vs_lookup_step_alt[OF _ _ vs_refs_pml4I],
                simp add: ucast_ucast_mask9, fastforce\<close>)
    prefer 3 subgoal
      by (rule exI[of _ X64HugePage]; frule (3) valid_vspace_objs_entryD;
          clarsimp simp: bit_simps vmsz_aligned_def)
   apply (all \<open>drule (2) vs_lookup_step_alt[OF _ _ vs_refs_pdptI], fastforce\<close>)
   prefer 2 subgoal
     by (rule exI[of _ X64LargePage]; frule (3) valid_vspace_objs_entryD;
         clarsimp simp: bit_simps vmsz_aligned_def)
  apply (drule (2) vs_lookup_step_alt[OF _ _ vs_refs_pdI], fastforce)
  by (rule exI[of _ X64SmallPage]; frule (3) valid_vspace_objs_entryD;
      clarsimp simp: bit_simps vmsz_aligned_def) *)

lemma user_mem_dom_cong:
  "kheap s = kheap s' \<Longrightarrow> dom (user_mem s) = dom (user_mem s')"
  by (simp add: user_mem_def in_user_frame_def dom_def obj_at_def)

lemma device_mem_dom_cong:
  "kheap s = kheap s' \<Longrightarrow> dom (device_mem s) = dom (device_mem s')"
  by (simp add: device_mem_def in_device_frame_def dom_def obj_at_def)

lemma device_frame_in_device_region:
  "\<lbrakk>in_device_frame p s; pspace_respects_device_region s\<rbrakk>
  \<Longrightarrow> device_state (machine_state s) p \<noteq> None"
  by (auto simp add: pspace_respects_device_region_def dom_def device_mem_def)

global_naming Arch
named_theorems AInvsPre_asms

lemma ptable_rights_imp_frame[AInvsPre_asms]:
  assumes "valid_state s"
  shows "ptable_rights t s x \<noteq> {} \<Longrightarrow>
         ptable_lift t s x = Some (addrFromPPtr y) \<Longrightarrow>
         in_user_frame y s \<or> in_device_frame y s"
  sorry (* FIXME RISCV
  apply (rule ccontr, frule ptable_lift_Some_canonical_addressD)
  using assms
  apply (clarsimp simp: ptable_lift_def ptable_rights_def
                        in_user_frame_def in_device_frame_def
                 split: option.splits)
  apply (case_tac "x \<in> kernel_mappings")
   apply (frule (2) some_get_page_info_kmapsD; fastforce simp: valid_state_def)
  apply (frule some_get_page_info_umapsD)
        apply (rule get_vspace_of_thread_reachable)
        apply clarsimp
        apply (frule get_page_info_gpd_kmaps[rotated 2])
           apply (simp_all add: valid_state_def valid_pspace_def
                                valid_arch_state_def)
    apply (clarsimp simp: data_at_def)+
  apply (drule_tac x=sz in spec)+
  apply (rename_tac p_addr attr rghts sz)
  apply (frule is_aligned_add_helper[OF _ and_mask_less', THEN conjunct2, of _ _ x])
   apply (simp only: pbfs_less_wb'[simplified word_bits_def])
  apply (clarsimp simp: data_at_def ptrFromPAddr_def addrFromPPtr_def field_simps)
  apply (subgoal_tac "p_addr + (pptrBase + (x && mask (pageBitsForSize sz)))
                        && ~~ mask (pageBitsForSize sz) = p_addr + pptrBase")
   apply simp
  apply (subst add.assoc[symmetric])
  apply (subst is_aligned_add_helper)
    apply (erule aligned_add_aligned)
     apply (case_tac sz; simp add: is_aligned_def pptrBase_def bit_simps)
    apply simp
   apply (rule and_mask_less')
   apply (case_tac sz; simp add: bit_simps)
  apply simp
  done *)

end

interpretation AInvsPre?: AInvsPre
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact AInvsPre_asms)?)
  qed

requalify_facts
  RISCV64.user_mem_dom_cong
  RISCV64.device_mem_dom_cong
  RISCV64.device_frame_in_device_region

end
