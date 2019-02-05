(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
RISCV-specific VSpace invariants
*)

theory ArchVSpace_AI
imports "../VSpacePre_AI"
begin

context Arch begin global_naming RISCV64

crunch pspace_in_kernel_window[wp]: perform_page_invocation "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)

lemma asid_low_high_bits:
  "\<lbrakk> x && mask asid_low_bits = y && mask asid_low_bits;
    ucast (asid_high_bits_of x) = (ucast (asid_high_bits_of y)::machine_word);
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule word_eqI)
  apply (simp add: upper_bits_unset_is_l2p_64[symmetric] bang_eq nth_ucast word_size)
  apply (clarsimp simp: asid_high_bits_of_def nth_ucast nth_shiftr)
  apply (simp add: asid_high_bits_def asid_bits_def asid_low_bits_def word_bits_def)
  subgoal premises prems[rule_format] for n
  apply (cases "n < 10")
   using prems(1)
   apply fastforce
  apply (cases "n < 16")
   using prems(2)[where n="n - 10"]
   apply fastforce
  using prems(3-)
  by (simp add: linorder_not_less)
  done

lemma asid_low_high_bits':
  "\<lbrakk> ucast x = (ucast y :: 10 word);
    asid_high_bits_of x = asid_high_bits_of y;
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule asid_low_high_bits)
     apply (rule word_eqI)
     apply (subst (asm) bang_eq)
     apply (simp add: nth_ucast asid_low_bits_def word_size)
    apply (rule word_eqI)
    apply (subst (asm) bang_eq)+
    apply (simp add: nth_ucast asid_low_bits_def)
   apply assumption+
  done


lemma pt_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid' pt s;
     unique_table_refs s;
     valid_vs_lookup s; valid_vspace_objs s; valid_global_objs s;
     valid_arch_state s; asid < 2 ^ asid_bits; asid' < 2 ^ asid_bits \<rbrakk>
       \<Longrightarrow> asid = asid'"
  sorry (* FIXME RISCV: being proved in ArchAcc, check there
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule(1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])+
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric])
  apply (clarsimp simp: table_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  apply (drule(2) unique_table_refsD,
         simp+, clarsimp simp: table_cap_ref_def,
         erule(1) asid_low_high_bits)
   apply simp+
  done *)

lemma pt_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid pt' s \<rbrakk> \<Longrightarrow> pt = pt'"
  by (clarsimp simp: vspace_at_asid_def)

lemma dmo_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_asid_def)
  done


crunch valid_vs_lookup[wp]: do_machine_op "valid_vs_lookup"


lemmas ackInterrupt_irq_masks = no_irq[OF no_irq_ackInterrupt]


find_theorems sfence device_state

crunches sfence, hwASIDFlush, setVSpaceRoot
  for underlying_memory_inv[wp]: "\<lambda>ms. P (underlying_memory ms)"


lemma ucast_ucast_low_bits:
  fixes x :: machine_word
  shows "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> ucast (ucast x:: asid_low_index) = x"
  apply (simp add: ucast_ucast_mask)
  apply (rule less_mask_eq)
  apply (subst (asm) word_less_sub_le)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_low_bits_def)
  done

lemma asid_high_bits_of_or:
  "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> asid_high_bits_of (base || x) = asid_high_bits_of base"
  apply (rule word_eqI)
  apply (drule le_2p_upper_bits)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_high_bits_of_def word_size nth_ucast nth_shiftr asid_low_bits_def word_bits_def)
  done

lemma vs_lookup_clear_asid_table:
  "vs_lookup (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
             bot_level asid vref  = Some (level, p)
   \<Longrightarrow> vs_lookup s bot_level asid vref = Some (level, p)"
  sorry (* FIXME RISCV *)


lemma vs_lookup_pages_clear_asid_table:
  "vs_lookup_pages (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
             bot_level asid vref  = Some (level, p)
   \<longrightarrow> vs_lookup_pages s bot_level asid vref = Some (level, p)"
  sorry (* FIXME RISCV *)


lemma valid_arch_state_unmap_strg:
  "valid_arch_state s \<longrightarrow>
   valid_arch_state(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (rule conjI)
   apply (clarsimp simp add: ran_def)
   apply blast
  apply (clarsimp simp: inj_on_def)
  done


lemma valid_vspace_objs_unmap_strg:
  "valid_vspace_objs s \<longrightarrow>
   valid_vspace_objs(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (drule vs_lookup_clear_asid_table[rule_format])
  apply blast
  done


lemma valid_vs_lookup_unmap_strg:
  "valid_vs_lookup s \<longrightarrow>
   valid_vs_lookup(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vs_lookup_def)
  apply (drule vs_lookup_pages_clear_asid_table[rule_format])
  apply blast
  done


lemma ex_asid_high_bits_plus:
  "asid \<le> mask asid_bits \<Longrightarrow> \<exists>x \<le> 2^asid_low_bits - 1. asid = (ucast (asid_high_bits_of asid) << asid_low_bits) + x"
  apply (rule_tac x="asid && mask asid_low_bits" in exI)
  apply (rule conjI)
   apply (simp add: mask_def)
   apply (rule word_and_le1)
  apply (subst (asm) mask_def)
  apply (simp add: upper_bits_unset_is_l2p_64[symmetric])
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_ucast nth_shiftl)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr asid_high_bits_of_def
                        asid_low_bits_def word_bits_def asid_bits_def)
  apply (rule iffI)
   prefer 2
   apply fastforce
  apply (clarsimp simp: linorder_not_less)
  apply (rule conjI)
   prefer 2
   apply arith
  apply (subgoal_tac "n < 16", simp)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


lemma asid_high_bits_shl:
  "\<lbrakk> is_aligned base asid_low_bits; base \<le> mask asid_bits \<rbrakk> \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  apply (simp add: mask_def upper_bits_unset_is_l2p_64 [symmetric])
  apply (rule word_eqI[rule_format])
  apply (simp add: is_aligned_nth nth_ucast nth_shiftl nth_shiftr asid_low_bits_def
                   asid_high_bits_of_def word_size asid_bits_def word_bits_def)
  apply (rule iffI, clarsimp)
  apply (rule context_conjI)
   apply (clarsimp simp add: linorder_not_less [symmetric])
  apply simp
  apply (rule conjI)
   prefer 2
   apply simp
  apply (subgoal_tac "n < 16", simp)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


lemma valid_asid_map_unmap:
  "valid_asid_map s \<and> is_aligned base asid_low_bits \<and> base \<le> mask asid_bits \<longrightarrow>
   valid_asid_map(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_asid_map_def)


lemma asid_low_bits_word_bits:
  "asid_low_bits < word_bits"
  by (simp add: asid_low_bits_def word_bits_def)

lemma valid_vs_lookup_arch_update:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<and>
   riscv_kernel_vspace (f (arch_state s)) = riscv_kernel_vspace (arch_state s)
     \<Longrightarrow> valid_vs_lookup (arch_state_update f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def)

lemma store_pte_vspace_at_asid:
  "store_pte p pte \<lbrace>vspace_at_asid asid pt\<rbrace>"
  sorry (* FIXME RISCV *)

crunch "distinct" [wp]: store_pte pspace_distinct

definition valid_unmap :: "vmpage_size \<Rightarrow> asid * vspace_ref \<Rightarrow> bool" where
  "valid_unmap sz \<equiv> \<lambda>(asid, vptr). 0 < asid \<and> is_aligned vptr (pageBitsForSize sz)"

definition
  "parent_for_refs \<equiv> \<lambda>(_, slot) cap. cap = ArchObjectCap (PageTableCap (table_base slot) None)"

definition
  "same_ref \<equiv> \<lambda>(pte, slot) cap s.
     (\<exists>p. pte_ref pte = Some p \<and> obj_refs cap = {p}) \<and>
     (\<forall>level asid vref. vs_lookup_table level asid vref s = Some (level, slot) \<longrightarrow>
                        vs_cap_ref cap = Some (asid, vref_for_level vref level))"
  (* FIXME RISCV: level might be off by one. We want the part of the vref that goes to the slot,
                  not only to the beginning of the table *)

definition
  "valid_page_inv pg_inv \<equiv> case pg_inv of
    PageMap cap ptr m \<Rightarrow>
      cte_wp_at (is_arch_update (ArchObjectCap cap) and ((=) None \<circ> vs_cap_ref)) ptr
      and cte_wp_at is_frame_cap ptr
      and (\<lambda>s. same_ref m (ArchObjectCap cap) s)
      and valid_slots m
      and valid_arch_cap cap
      and K (is_PagePTE (fst m))
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
  | PageRemap m \<Rightarrow>
      valid_slots m and K (is_PagePTE (fst m))
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
      and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>cap. same_ref m cap s) slot s)
  | PageUnmap cap ptr \<Rightarrow>
     \<lambda>s. \<exists>dev r R sz m. cap = FrameCap r R sz dev m \<and>
         case_option True (valid_unmap sz) m \<and>
         cte_wp_at (is_arch_diminished (ArchObjectCap cap)) ptr s \<and>
         valid_arch_cap cap s
  | PageGetAddr ptr \<Rightarrow> \<top>"

definition
  "valid_pti pti \<equiv> case pti of
     PageTableMap cap ptr pde p \<Rightarrow>
     pde_at p and (\<lambda>s. wellformed_pde pde) and
     valid_pde pde and valid_cap cap and
     cte_wp_at (\<lambda>c. is_arch_update cap c \<and> cap_asid c = None) ptr and
     empty_pde_at p and
     (\<lambda>s. \<exists>p' ref. vs_cap_ref cap = Some (VSRef (p && mask pd_bits >> 2) (Some APageDirectory) # ref)
              (* \<and> (ref \<rhd> (p && ~~ mask pd_bits)) s *)
              \<and> pde_ref pde = Some p' \<and> p' \<in> obj_refs cap
              \<and> (\<exists>ao. ko_at (ArchObj ao) p' s \<and> valid_vspace_obj ao s)
              \<and> hd (the (vs_cap_ref cap)) \<notin> kernel_vsrefs) and
     K (is_pt_cap cap \<and> cap_asid cap \<noteq> None)
   | PageTableUnmap cap ptr \<Rightarrow>
     cte_wp_at (\<lambda>c. is_arch_diminished cap c) ptr and valid_cap cap
       and is_final_cap' cap
       and K (is_pt_cap cap)"


crunches unmap_page
  for aligned [wp]: pspace_aligned
  and "distinct" [wp]: pspace_distinct
  and valid_objs[wp]: valid_objs
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)


lemma set_cap_valid_slots[wp]:
  "set_cap cap p \<lbrace>valid_slots slots\<rbrace>"
  apply (cases slots, clarsimp simp: valid_slots_def)
  apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
  sorry (* FIXME RISCV
  apply (clarsimp simp:valid_slots_def)
  apply (wp hoare_vcg_ball_lift)
  done *)

crunch aligned [wp]: unmap_page_table pspace_aligned
  (wp: crunch_wps)


crunch valid_objs [wp]: unmap_page_table valid_objs
  (wp: crunch_wps simp: crunch_simps)


crunch "distinct" [wp]: unmap_page_table pspace_distinct
  (wp: crunch_wps simp: crunch_simps)


crunch caps_of_state [wp]: unmap_page_table "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)


crunch typ_at [wp]: unmap_page_table "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps hoare_drop_imps)


definition
  "valid_apinv ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow>
  (\<lambda>s. \<exists>pool. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) p s \<and>
              pool (ucast asid) = None)
  and cte_wp_at (\<lambda>cap. is_pd_cap cap \<and> cap_asid cap = None) slot
  and K (0 < asid \<and> asid \<le> 2^asid_bits - 1)
  and ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p)"

lemma store_hw_asid_invs:
  "\<lbrace>invs and
   (\<lambda>s. arm_asid_map (arch_state s) asid = None \<and>
        arm_hwasid_table (arch_state s) hw_asid = None \<and>
        asid \<le> mask asid_bits)\<rbrace>
  store_hw_asid asid hw_asid
  \<lbrace>\<lambda>x. invs\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule store_hw_asid_valid_arch)
   apply fastforce
  apply (simp add: store_hw_asid_def)
  apply (wp find_pd_for_asid_assert_wp)
  apply (clarsimp simp: invs_def valid_state_def)
  apply (simp add: valid_global_refs_def global_refs_def
                   valid_irq_node_def valid_vspace_objs_arch_update
                   valid_global_objs_def valid_arch_caps_def second_level_tables_def
                   valid_table_caps_def valid_kernel_mappings_def
                   valid_machine_state_def valid_vs_lookup_arch_update)
  apply (simp add: valid_asid_map_def fun_upd_def[symmetric]
                   pd_at_asid_arch_up)
  done

lemma invalidateLocalTLB_ASID_valid_irq_states:
  "\<lbrace>\<lambda>m. valid_irq_states (s\<lparr>machine_state := m\<rparr>)\<rbrace> invalidateLocalTLB_ASID x
   \<lbrace>\<lambda>a b. valid_irq_states (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  apply(simp add: valid_irq_states_def | wp no_irq | simp add: no_irq_invalidateLocalTLB_ASID)+
  done

lemma find_free_hw_asid_invs [wp]:
  "\<lbrace>invs\<rbrace> find_free_hw_asid \<lbrace>\<lambda>asid. invs\<rbrace>"
  apply (rule hoare_add_post)
    apply (rule find_free_hw_asid_valid_arch)
   apply fastforce
  apply (simp add: find_free_hw_asid_def invalidate_hw_asid_entry_def invalidate_asid_def
                   do_machine_op_def split_def
              cong: option.case_cong)
  apply (wp|wpc)+
  apply (clarsimp simp: invs_def valid_state_def split del: if_split)
  apply (simp add: valid_global_refs_def global_refs_def cur_tcb_def
                   valid_irq_node_def valid_vspace_objs_arch_update
                   valid_global_objs_def valid_arch_caps_def second_level_tables_def
                   valid_table_caps_def valid_kernel_mappings_def
                   valid_machine_state_def valid_vs_lookup_arch_update)
  apply (elim conjE)
  apply (rule conjI)
   apply(erule use_valid[OF _ invalidateLocalTLB_ASID_valid_irq_states])
   apply fastforce
  apply(rule conjI)
   apply clarsimp
   apply (drule use_valid)
     apply (rule_tac p=p in invalidateLocalTLB_ASID_underlying_memory, simp, fastforce)
  apply (clarsimp simp: valid_asid_map_def fun_upd_def[symmetric]
                        pd_at_asid_arch_up')
  apply (rule conjI, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule_tac P1 = "(=) (device_state (machine_state s))" in
    use_valid[OF _ invalidateLocalTLB_ASID_device_state_inv])
   apply simp
  apply clarsimp
  done

lemma get_hw_asid_invs [wp]:
  "\<lbrace>invs and K (a \<le> mask asid_bits)\<rbrace> get_hw_asid a \<lbrace>\<lambda>hw_asid. invs\<rbrace>"
  apply (simp add: get_hw_asid_def)
  apply (wp store_hw_asid_invs load_hw_asid_wp|wpc)+
  apply simp
  done

lemma arm_context_switch_invs [wp]:
  "\<lbrace>invs and K (a \<le> mask asid_bits)\<rbrace> arm_context_switch pd a \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: arm_context_switch_def)
  apply (wp dmo_invs)
  apply (rule hoare_post_imp[rotated])
  apply (rule get_hw_asid_invs[simplified])
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: setHardwareASID_def set_current_pd_def writeTTBR0_def
                            isb_def dsb_def machine_op_lift_def
                            machine_rest_lift_def split_def | wp)+)[3]
  apply(erule use_valid)
   apply(wp no_irq | simp add: no_irq_setHardwareASID no_irq_set_current_pd)+
  done

lemmas set_current_pd_irq_masks = no_irq[OF no_irq_set_current_pd]
lemmas setHardwareASID_irq_masks = no_irq[OF no_irq_setHardwareASID]

lemma dmo_set_current_pd_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op (set_current_pd addr) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: set_current_pd_def writeTTBR0_def dsb_def isb_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ set_current_pd_irq_masks])
  done

crunch device_state_inv[wp]: ackInterrupt "\<lambda>ms. P (device_state ms)"
lemma dmo_ackInterrupt[wp]: "\<lbrace>invs\<rbrace> do_machine_op (ackInterrupt irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: ackInterrupt_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ ackInterrupt_irq_masks])
  done

crunch device_state_inv[wp]: setIRQTrigger "\<lambda>ms. P (device_state ms)"

lemma dmo_setIRQTrigger_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op (setIRQTrigger irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: setIRQTrigger_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ setIRQTrigger_irq_masks])
  done

lemma svr_invs [wp]:
  "\<lbrace>invs\<rbrace> set_vm_root t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp find_pd_for_asid_inv hoare_vcg_all_lift | wpc | simp add: split_def)+
    apply (rule_tac Q'="\<lambda>_ s. invs s \<and> x2 \<le> mask asid_bits" in hoare_post_imp_R)
     prefer 2
     apply simp
    apply (rule valid_validE_R)
    apply (wp find_pd_for_asid_inv | simp add: split_def)+
   apply (rule_tac Q="\<lambda>c s. invs s \<and> s \<turnstile> c" in hoare_strengthen_post)
    apply wp
   apply (clarsimp simp: valid_cap_def mask_def)
  apply(simp add: invs_valid_objs)
  done

crunch pred_tcb_at[wp]: set_vm_root "pred_tcb_at proj P t"
  (simp: crunch_simps)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done


lemma set_cap_valid_pte_stronger:
  "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)

end

locale vs_lookup_map_some_pdes = Arch +
  fixes pd pdp s s' S T pd'
  defines "s' \<equiv> s\<lparr>kheap := kheap s(pdp \<mapsto> ArchObj (PageDirectory pd'))\<rparr>"
  assumes refs: "vs_refs (ArchObj (PageDirectory pd')) =
                 (vs_refs (ArchObj (PageDirectory pd)) - T) \<union> S"
  assumes old: "kheap s pdp = Some (ArchObj (PageDirectory pd))"
  assumes pts: "\<forall>x \<in> S. page_table_at (snd x) s"
begin

definition
  "new_lookups \<equiv> {((rs,p),(rs',p')). \<exists>r. rs' = r # rs \<and> (r,p') \<in> S \<and> p = pdp}"


lemma vs_lookup1:
  "vs_lookup1 s' \<subseteq> vs_lookup1 s \<union> new_lookups"
  apply (simp add: vs_lookup1_def)
  apply (clarsimp simp: obj_at_def s'_def new_lookups_def)
  apply (auto split: if_split_asm simp: refs old)
  done


lemma vs_lookup_trans:
  "(vs_lookup1 s')^* \<subseteq> (vs_lookup1 s)^* \<union> (vs_lookup1 s)^* O new_lookups^*"
  apply (rule ord_le_eq_trans, rule rtrancl_mono, rule vs_lookup1)
  apply (rule union_trans)
  apply (clarsimp simp add: new_lookups_def)
  apply (drule bspec [OF pts])
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def)
  done


lemma double_new_lookup:
  "\<lbrakk> (x, y) \<in> new_lookups; (y, z) \<in> new_lookups \<rbrakk> \<Longrightarrow> False"
  by (auto simp: new_lookups_def obj_at_def old a_type_def
          dest!: bspec [OF pts])


lemma new_lookups_trans:
  "new_lookups^* = (new_lookups \<union> Id)"
  apply (rule set_eqI, clarsimp, rule iffI)
   apply (erule rtranclE)
    apply simp
   apply (erule rtranclE)
    apply simp
   apply (drule(1) double_new_lookup)
   apply simp
  apply auto
  done


lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)


lemma vs_lookup:
  "vs_lookup s' \<subseteq> vs_lookup s \<union> new_lookups^* `` vs_lookup s"
  unfolding vs_lookup_def
  apply (rule order_trans)
   apply (rule Image_mono [OF _ order_refl])
   apply (rule vs_lookup_trans)
  apply (clarsimp simp: relcomp_Image Un_Image)
  done

lemma vs_lookup2:
  "vs_lookup s' \<subseteq> vs_lookup s \<union> (new_lookups `` vs_lookup s)"
  apply (rule order_trans, rule vs_lookup)
  apply (auto simp add: vs_lookup new_lookups_trans)
  done


end

context Arch begin global_naming RISCV64

lemma set_pd_vspace_objs_map:
  notes valid_vspace_obj.simps[simp del] and a_type_elims[rule del]
  shows
  "\<lbrace>valid_vspace_objs and
   obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko - T \<union> S) p and
   (\<lambda>s. \<forall>x \<in> S. page_table_at (snd x) s) and
   (\<lambda>s. \<forall>(r,p') \<in> S. \<forall>ao. (\<exists>\<rhd>p) s \<longrightarrow> ko_at (ArchObj ao) p' s
                      \<longrightarrow> valid_vspace_obj ao s) and
   (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s)\<rbrace>
  set_pd p pd \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_vspace_objs_def
           simp del: fun_upd_apply
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (1) vs_lookup_map_some_pdes.intro, simp add: obj_at_def)
  apply (frule vs_lookup_map_some_pdes.vs_lookup2)
  apply (drule(1) subsetD)
  apply (erule UnE)
   apply (simp only: fun_upd_apply split: if_split_asm)
    apply (rule valid_vspace_obj_same_type)
      apply fastforce
     apply assumption
    apply (clarsimp simp add: a_type_def)
   apply (rule valid_vspace_obj_same_type)
     apply fastforce
    apply assumption
   apply (clarsimp simp: a_type_def)
  apply (clarsimp simp add: vs_lookup_map_some_pdes.new_lookups_def)
  apply (drule(1) bspec)+
  apply (clarsimp simp add: a_type_simps  split: if_split_asm)
  apply (drule mp, erule exI)+
  apply (erule(1) valid_vspace_obj_same_type)
  apply (simp add: a_type_def)
  done

(* FIXME: move *)
lemma simpler_set_pd_def:
  "set_pd p pd =
   (\<lambda>s. if \<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd))
        then ({((), s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageDirectory pd))\<rparr>)},
              False)
        else ({}, True))"
  by (rule ext)
     (auto simp: set_pd_def get_object_def simpler_gets_def assert_def
                 return_def fail_def set_object_def get_def put_def bind_def
          split: Structures_A.kernel_object.split arch_kernel_obj.split)

lemma set_pd_valid_vs_lookup_map:
  "\<lbrace>valid_vs_lookup and valid_arch_state and valid_vspace_objs and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) =
                 vs_refs ko - T \<union> S) p and
    (\<lambda>s. \<forall>x\<in>S. page_table_at (snd x) s) and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) =
                 vs_refs_pages ko - T' \<union> S') p and
    (\<lambda>s. \<forall>(r, p')\<in>S. \<forall>ao. (\<exists>\<rhd> p) s \<longrightarrow>
                           ko_at (ArchObj ao) p' s \<longrightarrow> valid_vspace_obj ao s) and
    (\<lambda>s. (\<exists>\<rhd> p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c\<in>- kernel_mapping_slots. \<forall>q.
                 pde_ref_pages (pd c) = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast c) (Some APageDirectory) # r)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c\<in>- kernel_mapping_slots. \<forall>q.
                 pde_ref (pd c) = Some q \<longrightarrow>
                    (\<forall>q' pt d. ko_at (ArchObj (PageTable pt)) q s \<longrightarrow>
                        pte_ref_pages (pt d) = Some q' \<longrightarrow>
                        (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                  q' \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast d) (Some APageTable) #
               VSRef (ucast c) (Some APageDirectory) # r)))))\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  using set_pd_vspace_objs_map[where p=p and pd=pd and T=T and S=S]
        set_pd_valid_arch[of p pd]
  apply (clarsimp simp: valid_def simpler_set_pd_def)
  apply (drule_tac x=s in spec)+
  apply (clarsimp simp: valid_vs_lookup_def  split: if_split_asm)
  apply (subst caps_of_state_after_update[folded fun_upd_apply],
         simp add: obj_at_def)
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                            fun_upd_def)
     apply (drule_tac x=pa in spec)
     apply simp
     apply (drule vs_lookup_pages_atI)
     apply simp
    apply (drule_tac x=pa in spec)
    apply (drule_tac x="[VSRef (ucast b) (Some AASIDPool),
                         VSRef (ucast a) None]" in spec)+
    apply simp
    apply (drule vs_lookup_pages_apI)
      apply (simp split: if_split_asm)
     apply (simp+)[2]
   apply (frule_tac s="s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (PageDirectory pd))\<rparr>"
                 in vs_lookup_pages_pdI[rotated -1])
        apply (simp del: fun_upd_apply)+
   apply (frule vs_lookup_pages_apI)
     apply (simp split: if_split_asm)+
   apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)+
   apply (thin_tac "P \<longrightarrow> Q" for P Q)+
   apply (drule_tac x=pa in spec)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)
   apply (erule impE)
   apply (erule vs_lookup_pages_pdI)
     apply simp+
  apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)
  apply (thin_tac "P \<longrightarrow> Q" for P Q)+
  apply (case_tac "p=p\<^sub>2")
   apply (thin_tac "\<forall>p ref. P p ref" for P)
   apply (frule vs_lookup_pages_apI)
     apply (simp split: if_split_asm)
    apply simp+
   apply (drule spec, erule impE, assumption)
   apply (clarsimp split: if_split_asm)
   apply (drule bspec, fastforce)
   apply (simp add: pde_ref_def obj_at_def)
  apply (thin_tac "\<forall>r. (r \<unrhd> p) s \<longrightarrow> Q r" for Q)
  apply (clarsimp split: if_split_asm)
  apply (drule (7) vs_lookup_pages_ptI)
  apply simp
  done


lemma set_pd_valid_arch_caps:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_vspace_objs and
    valid_objs and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) =
                 vs_refs ko - T \<union> S) p and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) =
                 vs_refs_pages ko - T' \<union> S') p and
    (\<lambda>s. \<forall>x\<in>S. page_table_at (snd x) s) and
    (\<lambda>s. \<forall>p. (VSRef 0 (Some AASIDPool), p) \<notin> S) and
    (\<lambda>s. \<forall>(r, p')\<in>S. \<forall>ao. (\<exists>\<rhd> p) s \<longrightarrow>
                           ko_at (ArchObj ao) p' s \<longrightarrow> valid_vspace_obj ao s) and
    (\<lambda>s. (\<exists>\<rhd> p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    (\<lambda>s. (\<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pd_cap cap \<and>
                   p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None)
       \<or> (obj_at (empty_table (set (second_level_tables (arch_state s)))) p s \<longrightarrow>
                  empty_table (set (second_level_tables (arch_state s)))
                              (ArchObj (PageDirectory pd)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c\<in>- kernel_mapping_slots. \<forall>q.
                 pde_ref_pages (pd c) = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         q \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast c) (Some APageDirectory) # r)))) and
    (\<lambda>s. \<forall>r. (r \<unrhd> p) s \<longrightarrow>
             (\<forall>c\<in>- kernel_mapping_slots. \<forall>q.
                 pde_ref (pd c) = Some q \<longrightarrow>
                    (\<forall>q' pt d. ko_at (ArchObj (PageTable pt)) q s \<longrightarrow>
                        pte_ref_pages (pt d) = Some q' \<longrightarrow>
                        (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                  q' \<in> obj_refs cap \<and> vs_cap_ref cap =
         Some (VSRef (ucast d) (Some APageTable) #
               VSRef (ucast c) (Some APageDirectory) # r)))))\<rbrace>
   set_pd p pd
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def  simp del: fun_upd_apply
                 split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: valid_arch_caps_def)
  apply (subst caps_of_state_after_update[folded fun_upd_def],
         simp add: obj_at_def)+
  apply simp
  apply (rule conjI)
   using set_pd_valid_vs_lookup_map[where p=p and pd=pd and T=T and S=S
                                                     and T'=T' and S'=S']
   apply (clarsimp simp add: valid_def)
   apply (drule_tac x=s in spec)
   apply (simp add: simpler_set_pd_def obj_at_def)
  apply (simp add: valid_table_caps_def obj_at_def
                   caps_of_state_after_update[folded fun_upd_def]
              del: imp_disjL)
  apply (drule_tac x=p in spec, elim allEI, intro impI)
  apply clarsimp
  apply (erule_tac P="is_pd_cap cap" in disjE)
   prefer 2
   apply (frule_tac p="(a,b)" in caps_of_state_valid_cap, simp)
   apply (clarsimp simp add: is_pt_cap_def valid_cap_def obj_at_def
                             valid_arch_cap_def
                             a_type_def)
  apply (frule_tac cap=cap and cap'=capa and cs="caps_of_state s" in unique_table_caps_pdD)
        apply (simp add: is_pd_cap_def)+
    apply (clarsimp simp: is_pd_cap_def)+
  done

(* FIXME: move to wellformed *)
lemma global_pde_graph_ofI:
 " \<lbrakk>pd x = pde; pde_ref pde = Some v\<rbrakk>
  \<Longrightarrow> (x, v) \<in> graph_of (pde_ref o pd)"
  by (clarsimp simp: graph_of_def pde_ref_def comp_def)



lemma set_pd_valid_kernel_mappings_map:
  "\<lbrace>valid_kernel_mappings and
     obj_at (\<lambda>ko. glob_vs_refs (ArchObj (PageDirectory pd)) = glob_vs_refs ko - T \<union> S) p and
     (\<lambda>s. \<forall>(r,p) \<in> S. (r \<in> kernel_vsrefs)
                         = (p \<in> set (arm_global_pts (arch_state s))))\<rbrace>
     set_pd p pd
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_pd_def)
  apply (wp set_object_v_ker_map get_object_wp)
  apply (clarsimp simp: obj_at_def valid_kernel_mappings_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (drule bspec, erule ranI)
  apply (clarsimp simp: valid_kernel_mappings_if_pd_def
                        kernel_vsrefs_def)
  apply (drule_tac f="\<lambda>S. (VSRef (ucast x) (Some APageDirectory), r) \<in> S"
               in arg_cong)
  apply (simp add: glob_vs_refs_def)
  apply (drule iffD1)
   apply (rule image_eqI[rotated])
    apply (erule global_pde_graph_ofI[rotated])
    apply simp+
  apply (elim conjE disjE)
   apply (clarsimp dest!: graph_ofD)
  apply (drule(1) bspec)
  apply (clarsimp simp: kernel_base_shift_cast_le
                        kernel_mapping_slots_def)
  done

lemma glob_vs_refs_subset:
  " vs_refs x \<subseteq> glob_vs_refs x"
  apply (clarsimp simp: glob_vs_refs_def vs_refs_def)
  apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule pair_imageI)
  apply (simp add: graph_of_def split:if_split_asm)
  done

lemma vs_refs_pages_pdI:
  "\<lbrakk>pde_ref_pages (pd x) = Some a; x \<notin> kernel_mapping_slots\<rbrakk>
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), a) \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  by (auto simp: pde_ref_pages_def vs_refs_pages_def graph_of_def image_def split: pde.splits)

lemma pde_ref_pde_ref_pagesI[elim!]:
  "pde_ref (pd x) = Some a \<Longrightarrow> pde_ref_pages (pd x) = Some a"
  by (auto simp: pde_ref_def pde_ref_pages_def split: pde.splits)

lemma vs_refs_pdI2:
  "\<lbrakk>pd r = PageTablePDE x a b; r \<notin> kernel_mapping_slots\<rbrakk>
   \<Longrightarrow> (VSRef (ucast r) (Some APageDirectory), ptrFromPAddr x) \<in> vs_refs (ArchObj (PageDirectory pd))"
  by (auto simp: vs_refs_def pde_ref_def graph_of_def)


lemma set_pd_invs_map:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pde (pd i)) and
     obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko \<union> S) p and
     obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) = vs_refs_pages ko - T' \<union> S') p and
     obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')
                  \<and> (\<forall>x\<in>kernel_mapping_slots. pd x = pd' x)) p and
     (\<lambda>s. \<forall>(r,p) \<in> S. \<forall>ao. ko_at (ArchObj ao) p s \<longrightarrow> valid_vspace_obj ao s) and
     (\<lambda>s. \<forall>(r,p) \<in> S. page_table_at p s) and
     (\<lambda>s. \<forall>(r,p) \<in> S. (r \<in> kernel_vsrefs)
                         = (p \<in> set (arm_global_pts (arch_state s)))) and
     (\<lambda>s. \<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pd_cap cap
                  \<and> p \<in> obj_refs cap \<and> cap_asid cap \<noteq> None) and
     (\<lambda>s. \<forall>p. (VSRef 0 (Some AASIDPool), p) \<notin> S) and
     (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
              (\<forall>(r, p) \<in> S'. \<exists>p' cap. caps_of_state s p' = Some cap \<and> p \<in> obj_refs cap
                                       \<and> vs_cap_ref cap = Some (r # ref))) and
     (\<lambda>s. \<forall>ref. (ref \<unrhd> p) s \<longrightarrow>
              (\<forall>(r, p) \<in> S. (\<forall>q' pt d.
                      ko_at (ArchObj (PageTable pt)) p s \<longrightarrow>
                      pte_ref_pages (pt d) = Some q' \<longrightarrow>
                      (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                                q' \<in> obj_refs cap \<and>
                                vs_cap_ref cap =
                                Some (VSRef (ucast d) (Some APageTable) # r # ref))))) and

     valid_vspace_obj (PageDirectory pd)\<rbrace>
  set_pd p pd \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_pd_valid_objs set_pd_iflive set_pd_zombies
             set_pd_zombies_state_refs set_pd_valid_mdb set_pd_zombies_state_hyp_refs
             set_pd_valid_idle set_pd_ifunsafe set_pd_reply_caps
             set_pd_valid_arch set_pd_valid_global set_pd_cur
             set_pd_reply_masters valid_irq_node_typ
             set_pd_vspace_objs_map[where S=S and T="{}"]
             set_pd_valid_arch_caps[where S=S and T="{}" and S'=S' and T'=T']
             valid_irq_handlers_lift
             set_pd_valid_kernel_mappings_map[where S=S and T="{}"]
             set_pd_equal_kernel_mappings_triv)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (clarsimp simp: cap_range_def split_def)
  apply (rule conjI)
   apply clarsimp

   apply (drule (1) vs_refs_pages_pdI)
   apply (clarsimp simp: obj_at_def)
   apply (erule disjE)
    apply (clarsimp simp: valid_arch_caps_def)
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_step])
      apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
      apply (rule_tac x="VSRef (ucast c) (Some APageDirectory)" in exI)
      apply (erule conjI[OF refl])
     apply simp
    apply clarsimp
   apply (erule_tac x=r in allE, drule (1) mp, drule (1) bspec)
   apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pde_ref_def split: pde.splits)
   apply (drule (1) vs_refs_pdI2)
   apply (clarsimp simp: obj_at_def)
   apply (erule disjE)
    apply (clarsimp simp: valid_arch_caps_def)
    apply (drule valid_vs_lookupD[OF vs_lookup_pages_step[OF vs_lookup_pages_step]])
       apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
       apply (rule_tac x="VSRef (ucast c) (Some APageDirectory)" in exI)
       apply (rule conjI[OF refl])
       apply (erule subsetD[OF vs_refs_pages_subset])
      apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
      apply (rule_tac x="VSRef (ucast d) (Some APageTable)" in exI)
      apply (rule conjI[OF refl])
      apply (erule pte_ref_pagesD)
     apply simp
    apply clarsimp
   apply (erule_tac x=r in allE, drule (1) mp, drule_tac P="(%x. \<forall>q' pt . Q x q' pt y s)" for Q s in bspec)
   apply simp
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp add: obj_at_def glob_vs_refs_def)
   apply safe[1]
     apply (rule pair_imageI)
     apply (clarsimp simp add: graph_of_def)
     apply (case_tac "ab \<in> kernel_mapping_slots")
      apply clarsimp
     apply (frule (1) pde_graph_ofI[rotated])
      apply (case_tac "pd ab", simp_all)
     apply (clarsimp simp: vs_refs_def )
     apply (drule_tac x="(ab, bb)" and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))"
             in imageI)
     apply simp
     apply (erule imageE)
     apply (simp add: graph_of_def split_def)
    apply (rule pair_imageI)
    apply (case_tac "ab \<in> kernel_mapping_slots")
     apply (clarsimp simp add: graph_of_def)+
    apply (frule (1) pde_graph_ofI[rotated])
      apply (case_tac "pd ab", simp_all)
    apply (clarsimp simp: vs_refs_def )
    apply (drule_tac x="(ab, bb)" and f="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y))"
             in imageI)
    apply (drule_tac s="(\<lambda>(r, y). (VSRef (ucast r) (Some APageDirectory), y)) `
        graph_of
         (\<lambda>x. if x \<in> kernel_mapping_slots then None else pde_ref (pd x))" in sym)
    apply simp
    apply (drule_tac c="(VSRef (ucast ab) (Some APageDirectory), bb)" and B=S in UnI1)
    apply simp
    apply (erule imageE)
    apply (simp add: graph_of_def split_def)
   apply (subst (asm) Un_commute[where B=S])
   apply (drule_tac c="(aa,ba)" and B="vs_refs (ArchObj (PageDirectory pd'))" in UnI1)
   apply (drule_tac t="S \<union> vs_refs (ArchObj (PageDirectory pd'))" in sym)
   apply (simp del:Un_iff)
   apply (drule rev_subsetD[OF _ glob_vs_refs_subset])
   apply (simp add: glob_vs_refs_def)
  by blast

lemma vs_refs_add_one':
  "p \<notin> kernel_mapping_slots \<Longrightarrow>
   vs_refs (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))
       - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref (pd p))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  apply (simp add: vs_refs_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: if_split_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa,ba)" in image_eqI)
     apply simp
    apply (simp add: graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def split:if_split_asm)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done


lemma vs_refs_add_one:
  "\<lbrakk>pde_ref (pd p) = None; p \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   vs_refs (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  by (simp add: vs_refs_add_one')


lemma vs_refs_pages_add_one':
  "p \<notin> kernel_mapping_slots \<Longrightarrow>
   vs_refs_pages (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs_pages (ArchObj (PageDirectory pd))
       - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages (pd p))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages pde)"
  apply (simp add: vs_refs_pages_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: if_split_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa,ba)" in image_eqI)
     apply simp
    apply (simp add: graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def split:if_split_asm)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done

lemma vs_refs_pages_add_one:
  "\<lbrakk>pde_ref_pages (pd p) = None; p \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   vs_refs_pages (ArchObj (PageDirectory (pd (p := pde)))) =
   vs_refs_pages (ArchObj (PageDirectory pd))
       \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref_pages pde)"
  by (simp add: vs_refs_pages_add_one')

definition is_asid_pool_cap :: "cap \<Rightarrow> bool"
 where "is_asid_pool_cap cap \<equiv> \<exists>ptr asid. cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap ptr asid)"


(* FIXME: move *)
lemma valid_cap_to_pt_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; page_table_at p s\<rbrakk> \<Longrightarrow> is_pt_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pt_cap_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma ref_is_unique:
  "\<lbrakk>(ref \<rhd> p) s; (ref' \<rhd> p) s; p \<notin> set (arm_global_pts (arch_state s));
    valid_vs_lookup s; unique_table_refs (caps_of_state s);
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_caps (caps_of_state s) s\<rbrakk>
   \<Longrightarrow> ref = ref'"
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
    apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
      apply (clarsimp simp: valid_asid_table_def up_ucast_inj_eq)
      apply (erule (2) inj_on_domD)
     apply ((clarsimp simp: obj_at_def)+)[2]
   apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
     apply (clarsimp simp: obj_at_def)
    apply (drule (2) vs_lookup_apI)+
    apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                           obj_ref_elemD
                     simp: table_cap_ref_ap_eq[symmetric])
    apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
   apply (clarsimp simp: obj_at_def)
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
    apply ((clarsimp simp: obj_at_def)+)[2]
  apply (simp add: pde_ref_def split: pde.splits)
  apply (drule (5) vs_lookup_pdI)+
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                         obj_ref_elemD)
  apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
  apply (drule (3) valid_capsD[THEN valid_cap_to_pt_cap])+
  apply (clarsimp simp: is_pt_cap_def table_cap_ref_simps vs_cap_ref_simps)
  done

lemma mask_shift_mask_helper:
  "(p && mask pd_bits >> 2) && mask 12 = (p && mask pd_bits >> 2)"
  apply (rule word_eqI)
  apply (simp add: word_size pd_bits_def pageBits_def nth_shiftr conj_comms)
  done

lemma ucast_ucast_mask_shift_helper:
  "ucast (ucast (p && mask pd_bits >> 2 :: word32) :: 12 word)
        = (p && mask pd_bits >> 2 :: word32)"
  apply (rule ucast_ucast_len)
  apply (rule shiftr_less_t2n)
  apply (simp add: pd_bits_def pageBits_def)
  apply (rule order_less_le_trans, rule and_mask_less_size)
   apply (simp add: word_size)+
  done

lemma unat_ucast_pd_bits_shift:
  "unat (ucast ((p :: word32) && mask pd_bits >> 2) :: 12 word)
       = unat (p && mask pd_bits >> 2)"
  apply (simp only: unat_ucast)
  apply (rule mod_less)
  apply (rule unat_less_power)
   apply (simp add: word_bits_def)
  apply (rule shiftr_less_t2n)
  apply (rule order_le_less_trans [OF word_and_le1])
  apply (simp add: pd_bits_def pageBits_def mask_def)
  done

lemma kernel_vsrefs_kernel_mapping_slots:
  "(ucast (p && mask pd_bits >> 2) \<in> kernel_mapping_slots) =
    (VSRef (p && mask pd_bits >> 2) (Some APageDirectory) \<in> kernel_vsrefs)"
  by (clarsimp simp: kernel_mapping_slots_def kernel_vsrefs_def
                     word_le_nat_alt unat_ucast_pd_bits_shift
                     kernel_base_def)

lemma vs_lookup_typI:
  "\<lbrakk>(r \<rhd> p) s; valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> page_table_at p s
    \<or> page_directory_at p s
    \<or> asid_pool_at p s"
  apply (erule (1) vs_lookupE_alt)
     apply (clarsimp simp: ran_def)
     apply (drule (2) valid_asid_tableD)
    apply simp+
  done

lemma vs_lookup_vs_lookup_pagesI':
  "\<lbrakk>(r \<unrhd> p) s; page_table_at p s \<or> page_directory_at p s \<or> asid_pool_at p s;
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> (r \<rhd> p) s"
 apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp:ran_def)
      apply (drule (2) valid_asid_tableD)
     apply (rule vs_lookupI)
      apply (fastforce simp: vs_asid_refs_def graph_of_def)
     apply simp
    apply (rule vs_lookupI)
     apply (fastforce simp: vs_asid_refs_def graph_of_def)
    apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
    apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule vs_lookupI)
    apply (fastforce simp: vs_asid_refs_def graph_of_def)
   apply (rule_tac y="([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None], p\<^sub>2)" in rtrancl_trans)
    apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
    apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule_tac x="(c, p)" in image_eqI)
    apply simp
   apply (fastforce simp: pde_ref_def pde_ref_pages_def valid_pde_def obj_at_def
                          a_type_def data_at_def
                   split: pde.splits if_splits arch_kernel_obj.splits)
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def graph_of_def)
  apply (rule_tac y="([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None], p\<^sub>2)" in rtrancl_trans)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (fastforce simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
  apply (rule_tac y="([VSRef (ucast c) (Some APageDirectory), VSRef (ucast b) (Some AASIDPool),
           VSRef (ucast a) None], (ptrFromPAddr addr))" in rtrancl_trans)
   apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
   apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def)
   apply (rule_tac x="(c,(ptrFromPAddr addr))" in image_eqI)
    apply simp
   apply (clarsimp simp: pde_ref_def)
  apply (rule rtrancl_into_rtrancl[OF rtrancl.intros(1)])
  apply (auto simp: data_at_def vs_lookup1_def obj_at_def vs_refs_def graph_of_def
                    pte_ref_pages_def a_type_def
             split: pte.splits if_splits arch_kernel_obj.splits)
  done

lemma vs_lookup_vs_lookup_pagesI:
  "\<lbrakk>(r \<rhd> p) s; (r' \<unrhd> p) s; valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> (r' \<rhd> p) s"
  by (erule (5) vs_lookup_vs_lookup_pagesI'[OF _ vs_lookup_typI])

(* FIXME: move *)
lemma valid_cap_to_pd_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; page_directory_at p s\<rbrakk> \<Longrightarrow> is_pd_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pd_cap_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma store_pde_map_invs:
  "\<lbrace>(\<lambda>s. wellformed_pde pde) and invs and empty_pde_at p and valid_pde pde
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p \<longrightarrow> (\<exists>ao. ko_at (ArchObj ao) p s \<and> valid_vspace_obj ao s))
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
               \<notin> kernel_vsrefs)
     and (\<lambda>s. \<exists>r. (r \<rhd> (p && (~~ mask pd_bits))) s \<and>
               (\<forall>p'. pde_ref_pages pde = Some p' \<longrightarrow>
                         (\<exists>p'' cap. caps_of_state s p'' = Some cap \<and> p' \<in> obj_refs cap
                                     \<and> vs_cap_ref cap = Some (VSRef (p && mask pd_bits >> 2) (Some APageDirectory) # r))
                         \<and> (\<forall>p''' a b. pde = PageTablePDE p''' a b \<longrightarrow>
                             (\<forall>pt. ko_at (ArchObj (PageTable pt)) (ptrFromPAddr p''') s \<longrightarrow>
                                    (\<forall>x word. pte_ref_pages (pt x) = Some word \<longrightarrow>
                                          (\<exists>p'' cap. caps_of_state s p'' = Some cap \<and> word \<in> obj_refs cap
                                                   \<and> vs_cap_ref cap =
                                                        Some (VSRef (ucast x) (Some APageTable)
                                                            # VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                                                            # r)))))))\<rbrace>
  store_pde p pde \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp dmo_invs set_pd_invs_map)
  apply clarsimp
  apply (rule conjI)
   apply (drule invs_valid_objs)
   apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def)
  apply (rule conjI)
   apply (clarsimp simp: empty_pde_at_def)
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_refs_add_one)
    subgoal by (simp add: pde_ref_def)
   subgoal by (simp add: kernel_vsrefs_kernel_mapping_slots)
  apply (rule conjI)
   apply (clarsimp simp: empty_pde_at_def)
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_refs_pages_add_one')
   subgoal by (simp add: kernel_vsrefs_kernel_mapping_slots)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def kernel_vsrefs_kernel_mapping_slots)
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def)
  apply (rule conjI)
   apply clarsimp
   subgoal by (case_tac pde, simp_all add: pde_ref_def)
  apply (rule conjI)
   apply (clarsimp simp: kernel_vsrefs_def
                         ucast_ucast_mask_shift_helper)
   apply (drule pde_ref_pde_ref_pagesI)
   apply clarsimp
   apply (drule valid_global_refsD2, clarsimp)
   apply (simp add: cap_range_def global_refs_def)
   apply blast
  apply (rule conjI)
   apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp+)
   apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
   apply (clarsimp dest!: obj_ref_elemD)
   apply (frule caps_of_state_valid_cap, clarsimp)
   apply (drule (1) valid_cap_to_pd_cap, simp add: obj_at_def a_type_simps)
   apply (thin_tac " \<forall>p. Q p \<longrightarrow> P p" for Q P)+
   subgoal by (simp add: is_pd_cap_def vs_cap_ref_def
                  split: cap.split_asm arch_cap.split_asm option.split_asm)
  apply (rule conjI)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule (2) ref_is_unique[OF _ vs_lookup_vs_lookup_pagesI])
           apply ((clarsimp simp: invs_def valid_state_def valid_arch_caps_def
                                  valid_arch_state_def)+)[2]
         apply (auto dest!: valid_global_ptsD [simplified second_level_tables_def] simp: obj_at_def )[1]
        apply clarsimp+
    apply (rule valid_objs_caps)
    apply clarsimp
   apply (simp add: ucast_ucast_mask mask_shift_mask_helper)
   apply auto[1]
  apply clarsimp
  apply (frule (1) valid_vspace_objsD, fastforce)
  apply clarsimp
  apply (drule pde_ref_pde_ref_pagesI)
  apply clarsimp
  apply (simp add: ucast_ucast_mask mask_shift_mask_helper)
  apply (clarsimp simp: pde_ref_pages_def obj_at_def
                 split: pde.splits)
  apply (erule_tac x=d in allE, erule_tac x=q' in allE)
  apply (frule (2) ref_is_unique[OF _ vs_lookup_vs_lookup_pagesI])
          apply ((clarsimp simp: invs_def valid_state_def valid_arch_caps_def
                                 valid_arch_state_def)+)[2]
        apply (auto dest!: valid_global_ptsD[simplified second_level_tables_def] simp: obj_at_def )[1]
       apply (clarsimp simp: data_at_def)+
     apply (rule valid_objs_caps)
     apply ((clarsimp elim!: impE)+)[2]
    apply (auto simp add: ucast_ucast_mask mask_shift_mask_helper
                          data_at_def obj_at_def)
  done

lemma set_cap_empty_pde:
  "\<lbrace>empty_pde_at p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. empty_pde_at p\<rbrace>"
  apply (simp add: empty_pde_at_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other hoare_vcg_ex_lift)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule conjI)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  done

lemma valid_cap_obj_ref_pt_pd:
  "\<lbrakk> s \<turnstile> cap; s \<turnstile> cap'; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> is_pt_cap cap')
         \<and> (is_pd_cap cap \<longrightarrow> is_pd_cap cap')"
  by (auto simp: is_cap_simps valid_cap_def
                 obj_at_def is_ep is_ntfn is_cap_table
                 is_tcb a_type_def
          split: cap.split_asm if_split_asm
                 arch_cap.split_asm option.split_asm)



lemma is_pt_pd_cap_asid_None_table_ref:
  "is_pt_cap cap \<or> is_pd_cap cap
     \<Longrightarrow> ((table_cap_ref cap = None) = (cap_asid cap = None))"
  by (auto simp: is_cap_simps table_cap_ref_def cap_asid_def
          split: option.split_asm)

lemma no_cap_to_obj_with_diff_ref_map:
  "\<lbrakk> caps_of_state s p = Some cap; is_pt_cap cap \<or> is_pd_cap cap;
     table_cap_ref cap = None;
     unique_table_caps (caps_of_state s);
     valid_objs s; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap[where p=p])
  apply (frule(1) caps_of_state_valid_cap[where p="(a, b)" for a b])
  apply (drule(1) valid_cap_obj_ref_pt_pd, simp)
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"])
      apply simp
     apply (simp add: is_pt_pd_cap_asid_None_table_ref)
    apply fastforce
   apply assumption
  apply simp
  done


lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemma mdb_cte_at_store_pte[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   store_pte y pte
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
    apply (simp add:store_pte_def set_pt_def)
    apply wp
    apply (rule hoare_drop_imp)
    apply (wp|simp)+
done

lemma valid_idle_store_pte[wp]:
  "\<lbrace>valid_idle\<rbrace> store_pte y pte \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add:store_pte_def)
  apply wp
  apply (rule hoare_vcg_precond_imp[where Q="valid_idle"])
  apply (simp add:set_pt_def)
  apply wp
  apply (simp add:get_object_def)
  apply wp
  apply (clarsimp simp:obj_at_def
    split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (fastforce simp:is_tcb_def)
  apply (assumption)
  apply (wp|simp)+
done

lemma mapM_swp_store_pte_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>p\<in>set slots. (\<exists>\<rhd> (p && ~~ mask pt_bits)) s) \<longrightarrow>
                  valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot. cte_wp_at
           (\<lambda>c. image (\<lambda>x. x && ~~ mask pt_bits) (set slots) \<subseteq> obj_refs c \<and>
                is_pt_cap c \<and> (pte = InvalidPTE \<or>
                               cap_asid c \<noteq> None)) slot s) and
   (\<lambda>s. \<forall>p\<in>set slots. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
              (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                   (\<exists>p' cap.
                       caps_of_state s p' = Some cap \<and>
                       q \<in> obj_refs cap \<and>
                       vs_cap_ref cap =
                       Some
                        (VSRef (p && mask pt_bits >> 2) (Some APageTable) #
                         ref))))\<rbrace>
     mapM (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp_all
  apply (wp mapM_wp' hoare_vcg_imp_lift hoare_vcg_ex_lift hoare_vcg_ball_lift
            hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply clarsimp
  apply (fastforce simp: cte_wp_at_caps_of_state is_pt_cap_def cap_asid_def)
  done

lemmas store_pde_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pde_caps_of_state]

crunch global_refs_inv[wp]: store_pde "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp) (* added by sjw, something dropped out of some set :( *)

lemma mapM_swp_store_pde_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots.
            ucast (sl && mask pd_bits >> 2) \<notin> kernel_mapping_slots) and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pde_invs_unmap hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply clarsimp+
  done

lemma vs_refs_pdI3:
  "\<lbrakk>pde_ref (pd x) = Some p; x \<notin> kernel_mapping_slots\<rbrakk>
   \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), p) \<in> vs_refs (ArchObj (PageDirectory pd))"
  by (auto simp: pde_ref_def vs_refs_def graph_of_def)


lemma set_pd_invs_unmap':
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pde (pd i)) and
    (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_vspace_obj (PageDirectory pd) s) and
    obj_at (\<lambda>ko. vs_refs (ArchObj (PageDirectory pd)) = vs_refs ko - T) p and
    obj_at (\<lambda>ko. vs_refs_pages (ArchObj (PageDirectory pd)) = vs_refs_pages ko - T' \<union> S') p and
    obj_at (\<lambda>ko. \<exists>pd'. ko = ArchObj (PageDirectory pd')
                       \<and> (\<forall>x \<in> kernel_mapping_slots. pd x = pd' x)) p and
    (\<lambda>s. p \<notin> global_refs s) and
    (\<lambda>s. \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and>
                   is_pd_cap cap \<and>
                   p \<in> obj_refs cap \<and> (\<exists>y. cap_asid cap = Some y)) and
    (\<lambda>s. \<forall>(a,b)\<in>S'. (\<forall>ref.
                  (ref \<unrhd> p) s \<longrightarrow>
                    (\<exists>p' cap.
                      caps_of_state s p' = Some cap \<and>
                      b \<in> obj_refs cap \<and> vs_cap_ref cap = Some (a # ref))))\<rbrace>
  set_pd p pd
  \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp set_pd_valid_objs set_pd_iflive set_pd_zombies
             set_pd_zombies_state_refs set_pd_valid_mdb
             set_pd_zombies_state_hyp_refs
             set_pd_valid_idle set_pd_ifunsafe set_pd_reply_caps
             set_pd_valid_arch set_pd_valid_global set_pd_cur
             set_pd_reply_masters valid_irq_node_typ
             set_pd_vspace_objs_unmap set_pd_valid_vs_lookup_map[where T=T and S="{}" and T'=T' and S'=S']
             valid_irq_handlers_lift
             set_pd_unmap_mappings set_pd_equal_kernel_mappings_triv)
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_arch_caps_def valid_objs_caps obj_at_def
    del: disjCI)
  apply (rule conjI, clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x="(VSRef (ucast c) (Some APageDirectory), q)" in ballE)
    apply clarsimp
   apply (frule (1) vs_refs_pages_pdI)
   apply (clarsimp simp: valid_arch_caps_def)
    apply (drule_tac p'=q and ref'="VSRef (ucast c) (Some APageDirectory) # r" in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
   apply (drule (1) valid_vs_lookupD)
   apply (clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) vs_refs_pdI3)
   apply clarsimp
   apply (drule_tac p'=q and ref'="VSRef (ucast c) (Some APageDirectory) # r" in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
    apply (erule subsetD[OF vs_refs_pages_subset])
   apply (drule_tac p'=q' and ref'="VSRef (ucast d) (Some APageTable) # VSRef (ucast c) (Some APageDirectory) # r"
                 in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
    apply (erule pte_ref_pagesD)
   apply (drule (1) valid_vs_lookupD)
   apply clarsimp
  apply auto
  done

lemma same_refs_lD:
  "\<lbrakk>same_refs (Inl(pte,p # slots)) cap s\<rbrakk>
 \<Longrightarrow> (\<exists>p. pte_ref_pages pte = Some p \<and> p \<in> obj_refs cap) \<and>
  (\<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
  vs_cap_ref cap = Some (VSRef (p && mask pt_bits >> 2) (Some APageTable) # ref))"
  by (clarsimp simp:same_refs_def split:list.splits)

lemma same_refs_rD:
  "\<lbrakk>same_refs (Inr(pde,p # slots)) cap s\<rbrakk>
 \<Longrightarrow>  (\<exists>p. pde_ref_pages pde = Some p \<and> p \<in> obj_refs cap) \<and>
         (\<forall>ref. (ref \<rhd> (p && ~~ mask pd_bits)) s \<longrightarrow>
               vs_cap_ref cap =
               Some (VSRef (p && mask pd_bits >> 2) (Some APageDirectory) # ref))"
   by (clarsimp simp:same_refs_def split:list.splits)

lemma store_pde_invs_unmap':
  "\<lbrace>invs
    and (\<exists>\<rhd> (p && ~~ mask pd_bits))
    and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs (Inr (pde, slots))) slot s)
    and (\<lambda>s. \<exists>ptr cap. caps_of_state s ptr = Some cap
                    \<and> is_pg_cap cap
                    \<and> same_refs (Inr (pde, slots)) cap s)
    and valid_pde pde
    and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)
    and K (wellformed_pde pde \<and> pde_ref pde = None)
    and K (ucast (p && mask pd_bits >> 2) \<notin> kernel_mapping_slots
           \<and> (\<exists>xs. slots = p # xs) )
    and (\<lambda>s. \<exists>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s)\<rbrace>
   store_pde p pde
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_name_pre_state)
   apply (clarsimp simp: store_pde_def | wp)+
    apply (rule_tac T ="  Pair (VSRef (p && mask pd_bits >> 2) (Some APageDirectory))
                        ` set_option (pde_ref (pd (ucast (p && mask pd_bits >> 2))))"
                and T'="  Pair (VSRef (p && mask pd_bits >> 2) (Some APageDirectory))
                        ` set_option (pde_ref_pages (pd (ucast (p && mask pd_bits >> 2))))"
                and S'="  Pair (VSRef (p && mask pd_bits >> 2) (Some APageDirectory))
                        ` set_option (pde_ref_pages pde)" in set_pd_invs_unmap')
  apply wp
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp add: invs_def valid_state_def valid_pspace_def
                             valid_objs_def valid_obj_def dom_def)
   apply (erule_tac P="\<lambda>x. (\<exists>y. a y x) \<longrightarrow> b x" for a b in allE[where x="(p && ~~ mask pd_bits)"])
   apply (erule impE)
    apply (clarsimp simp: obj_at_def vs_refs_def)+

  apply (rule conjI)
   apply (clarsimp simp add: invs_def valid_state_def valid_vspace_objs_def)
   apply (erule_tac P="\<lambda>x. (\<exists>y. a y x) \<longrightarrow> b x" for a b in allE[where x="(p && ~~ mask pd_bits)"])
   apply (erule impE)
    apply (erule_tac x=ref in exI)
   apply (erule_tac x="PageDirectory pd" in allE)
   apply (clarsimp simp: obj_at_def)

  apply (rule conjI)
   apply (safe)[1]
     apply (clarsimp simp add: vs_refs_def graph_of_def split: if_split_asm)
     apply (rule pair_imageI)
     apply (clarsimp)
    apply (clarsimp simp: vs_refs_def graph_of_def split: if_split_asm)
    apply (subst (asm) ucast_ucast_mask_shift_helper[symmetric], simp)
   apply (clarsimp simp: vs_refs_def graph_of_def split: if_split_asm)
   apply (rule_tac x="(ac, bc)" in image_eqI)
    apply clarsimp
   apply (clarsimp simp: ucast_ucast_mask_shift_helper ucast_id)

  apply (rule conjI)
   apply safe[1]
      apply (clarsimp simp: vs_refs_pages_def graph_of_def
                            ucast_ucast_mask_shift_helper ucast_id
                      split: if_split_asm)
      apply (rule_tac x="(ac, bc)" in image_eqI)
       apply clarsimp
      apply clarsimp
     apply (clarsimp simp: vs_refs_pages_def graph_of_def ucast_ucast_id
                     split: if_split_asm)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def
                    split: if_split_asm)
    apply (rule_tac x="(ac,bc)" in image_eqI)
     apply clarsimp
    apply (clarsimp simp: ucast_ucast_mask_shift_helper ucast_id)
   apply (clarsimp simp: vs_refs_pages_def graph_of_def)
   apply (rule_tac x="(ucast (p && mask pd_bits >> 2), x)" in image_eqI)
    apply (clarsimp simp: ucast_ucast_mask_shift_helper)
   apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state parent_for_refs_def)
   apply (drule same_refs_rD)
    apply (clarsimp split: list.splits)
   apply blast
  apply (drule same_refs_rD)
  apply clarsimp
  apply (drule spec, drule (2) mp[OF _ vs_lookup_vs_lookup_pagesI])
    apply ((clarsimp simp: invs_def valid_state_def valid_arch_state_def)+)[2]
  apply (rule_tac x=aa in exI, rule_tac x=ba in exI, rule_tac x=cap in exI)
  apply clarsimp
  done

lemma update_self_reachable:
  "\<lbrakk>(ref \<rhd> p) s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> (ref \<rhd> p) (s \<lparr>kheap := \<lambda>a. if a = p then Some y else kheap s a\<rparr>)"
  apply (erule (2) vs_lookupE_alt[OF _ _ valid_asid_table_ran])
    apply (rule vs_lookup_atI, clarsimp)
   apply (rule_tac ap=ap in vs_lookup_apI, auto simp: obj_at_def)[1]
  apply (clarsimp simp: pde_ref_def split: pde.splits)
  apply (rule_tac ap=ap and pd=pd in vs_lookup_pdI, auto simp: obj_at_def)[1]
  done

lemma update_self_reachable_pages:
  "\<lbrakk>(ref \<unrhd> p) s; valid_asid_table (arm_asid_table (arch_state s)) s;
    valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> (ref \<unrhd> p) (s \<lparr>kheap := \<lambda>a. if a = p then Some y else kheap s a\<rparr>)"
  apply (erule (2) vs_lookup_pagesE_alt[OF _ _ valid_asid_table_ran])
     apply (rule vs_lookup_pages_atI, clarsimp)
    apply (rule_tac ap=ap in vs_lookup_pages_apI, auto simp: obj_at_def)[1]
   apply (rule_tac ap=ap and pd=pd in vs_lookup_pages_pdI,
          auto simp: obj_at_def pde_ref_pages_def data_at_def
              split: pde.splits)[1]
  apply (rule_tac ap=ap and pd=pd in vs_lookup_pages_ptI,
          auto simp: obj_at_def pde_ref_pages_def pte_ref_pages_def data_at_def
              split: pde.splits pte.splits)[1]
  done


lemma pd_slots_helper:
  "\<lbrakk>a \<in> set slots; b \<in> set slots;
    cte_wp_at (parent_for_refs (Inr (pde, slots))) cptr s\<rbrakk>
   \<Longrightarrow> a && ~~ mask pd_bits = b && ~~ mask pd_bits"
  apply (clarsimp simp add: cte_wp_at_def parent_for_refs_def)
  apply (drule imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
  apply (drule imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
  apply (simp add: obj_refs_def)
  apply (case_tac cap, simp+)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap, simp+)
    apply (drule (1) set_rev_mp)
    apply (drule (1) set_rev_mp)
    apply force
   apply (drule (1) set_rev_mp)
   apply (drule (1) set_rev_mp)
   apply force
  apply (drule (1) set_rev_mp)
  apply (drule (1) set_rev_mp)
  apply force
  done

(* FIXME: move *)
lemma simpler_store_pde_def:
  "store_pde p pde s =
    (case kheap s (p && ~~ mask pd_bits) of
          Some (ArchObj (PageDirectory pd)) =>
            ({((), s\<lparr>kheap := (kheap s((p && ~~ mask pd_bits) \<mapsto>
                                       (ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 2) := pde))))))\<rparr>)}, False)
        | _ => ({}, True))"
  apply     (auto simp: store_pde_def simpler_set_pd_def get_object_def simpler_gets_def assert_def
                        return_def fail_def set_object_def get_def put_def bind_def get_pd_def
                  split: Structures_A.kernel_object.splits option.splits arch_kernel_obj.splits if_split_asm)
  done

lemma pde_update_valid_vspace_objs:
  "[|valid_vspace_objs s; valid_pde pde s; pde_ref pde = None; kheap s (p && ~~ mask pd_bits) = Some (ArchObj (PageDirectory pd))|]
   ==> valid_vspace_objs
         (s\<lparr>kheap := kheap s(p && ~~ mask pd_bits \<mapsto> ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 2) := pde))))\<rparr>)"
  apply (cut_tac pde=pde and p=p in store_pde_vspace_objs_unmap)
  apply (clarsimp simp: valid_def)
  apply (erule allE[where x=s])
  apply (clarsimp simp: split_def simpler_store_pde_def obj_at_def a_type_def
                  split: if_split_asm option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  done

lemma mapM_x_swp_store_pte_invs [wp]:
  "\<lbrace>invs and (\<lambda>s. (\<exists>p\<in>set slots. (\<exists>\<rhd> (p && ~~ mask pt_bits)) s) \<longrightarrow>
                  valid_pte pte s) and
    (\<lambda>s. wellformed_pte pte) and
    (\<lambda>s. \<exists>slot. cte_wp_at
           (\<lambda>c. image (\<lambda>x. x && ~~ mask pt_bits) (set slots) \<subseteq> obj_refs c \<and>
                is_pt_cap c \<and> (pte = InvalidPTE \<or>
                               cap_asid c \<noteq> None)) slot s) and
   (\<lambda>s. \<forall>p\<in>set slots. \<forall>ref. (ref \<rhd> (p && ~~ mask pt_bits)) s \<longrightarrow>
              (\<forall>q. pte_ref_pages pte = Some q \<longrightarrow>
                   (\<exists>p' cap.
                       caps_of_state s p' = Some cap \<and>
                       q \<in> obj_refs cap \<and>
                       vs_cap_ref cap =
                       Some
                        (VSRef (p && mask pt_bits >> 2) (Some APageTable) #
                         ref))))\<rbrace>
     mapM_x (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp)+

lemma mapM_x_swp_store_pde_invs_unmap:
  "\<lbrace>invs and K (\<forall>sl\<in>set slots.
                   ucast (sl && mask pd_bits >> 2) \<notin> kernel_mapping_slots) and
    (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM_x (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pde_invs_unmap)+

(* FIXME: move *)
lemma vs_cap_ref_table_cap_ref_None:
  "vs_cap_ref x = None \<Longrightarrow> table_cap_ref x = None"
  by (simp add: vs_cap_ref_def table_cap_ref_simps
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_pg_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> is_pg_cap c = is_pg_cap d"
  by (simp add: cap_master_cap_def is_pg_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_device_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> cap_is_device c = cap_is_device d"
  by (simp add: cap_master_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemmas vs_cap_ref_eq_imp_table_cap_ref_eq' =
       vs_cap_ref_eq_imp_table_cap_ref_eq[OF master_cap_eq_is_pg_cap_eq]

lemma arch_update_cap_invs_map:
  "\<lbrace>cte_wp_at (is_arch_update cap and
               (\<lambda>c. \<forall>r. vs_cap_ref c = Some r \<longrightarrow> vs_cap_ref cap = Some r)) p
             and invs and valid_cap cap\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (clarsimp simp: cte_wp_at_caps_of_state
              simp del: imp_disjL)
  apply (frule(1) valid_global_refsD2)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (clarsimp simp: is_cap_simps is_arch_update_def
              simp del: imp_disjL)
  apply (frule master_cap_cap_range, simp del: imp_disjL)
  apply (thin_tac "cap_range a = cap_range b" for a b)
  apply (rule conjI)
   apply (fastforce simp:is_valid_vtable_root_def vs_cap_ref_def split:arch_cap.splits vmpage_size.splits option.splits)
  apply (rule conjI)
   apply (rule ext)
   apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
  apply (rule context_conjI)
   apply (simp add: appropriate_cte_cap_irqs)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def cap_master_cap_def
                  split: cap.split)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def cap_master_cap_def
                  split: cap.split_asm)
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply simp
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply (case_tac "table_cap_ref capa =
                    table_cap_ref (ArchObjectCap a)")
    apply (frule unique_table_refs_no_cap_asidE[where S="{p}"])
     apply (simp add: valid_arch_caps_def)
    apply (simp add: no_cap_to_obj_with_diff_ref_def Ball_def)
   apply (case_tac "table_cap_ref capa")
    apply clarsimp
    apply (erule no_cap_to_obj_with_diff_ref_map,
           simp_all)[1]
      apply (clarsimp simp: table_cap_ref_def cap_master_cap_simps
                            is_cap_simps
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (erule vs_cap_ref_eq_imp_table_cap_ref_eq'[symmetric])
   apply (frule table_cap_ref_vs_cap_ref_Some)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply (erule disjE)
    apply (clarsimp simp: is_pt_cap_def cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
    apply (drule valid_table_capsD[OF caps_of_state_cteD])
       apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
      apply (simp add: is_pt_cap_def)
     apply (simp add: cap_asid_def)
    apply simp
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
   apply (drule valid_table_capsD[OF caps_of_state_cteD])
      apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
     apply (simp add: is_cap_simps)
    apply (simp add: cap_asid_def)
   apply simp
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)

  done

    (* Want something like
       cte_wp_at (\<lambda>c. \<forall>p'\<in>obj_refs c. \<not>(vs_cap_ref c \<unrhd> p') s \<and> is_arch_update cap c) p
       So that we know the new cap isn't clobbering a cap with necessary mapping info.
       invs is fine here (I suspect) because we unmap the page BEFORE we replace the cap.
    *)

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. (\<forall>p'\<in>obj_refs c. \<forall>ref. vs_cap_ref c = Some ref \<longrightarrow> \<not> (ref \<unrhd> p') s) \<and> is_arch_update cap c) p s)
             and invs and valid_cap cap
             and K (is_pg_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps
                        fun_eq_iff appropriate_cte_cap_irqs
                        is_pt_cap_def is_valid_vtable_root_def
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   subgoal by (simp add: cap_range_def)
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>r. vs_cap_ref c = Some r
                                \<longrightarrow> \<not> (r \<unrhd> obj_ref_of cap) s) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (simp add: final_cap_at_eq)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps is_valid_vtable_root_def
                        appropriate_cte_cap_irqs is_pt_cap_def
                        fun_eq_iff[where f="cte_refs cap" for cap]
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   apply (simp add: cap_range_def)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (simp add: cap_range_def gen_obj_refs_def image_def)
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply clarsimp
  apply fastforce
  done

lemma set_vm_root_for_flush_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  set_vm_root_for_flush pd asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: set_vm_root_for_flush_def)
  apply (wp hoare_drop_imps hoare_vcg_all_lift |wpc|simp)+
  done

lemma flush_table_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  flush_table pd asid vptr pt \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp dmo_invalidateLocalTLB_ASID_invs | simp)+
  apply (simp only: if_cancel
            | clarsimp simp: machine_op_lift_def
                             machine_rest_lift_def split_def
            | wp set_vm_root_for_flush_invs)+
  done

crunch vs_lookup[wp]: flush_table "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps)

crunch cte_wp_at[wp]: flush_table "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma global_refs_arch_update_eq:
  "\<lbrakk> arm_globals_frame (f (arch_state s)) = arm_globals_frame (arch_state s);
     arm_global_pd (f (arch_state s)) = arm_global_pd (arch_state s);
     arm_global_pts (f (arch_state s)) = arm_global_pts (arch_state s) \<rbrakk>
       \<Longrightarrow> global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

crunch global_refs_inv[wp]: flush_table "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps global_refs_arch_update_eq)

lemma lookup_pd_slot_kernel_mappings_strg:
  "is_aligned pd pd_bits \<and> vptr < kernel_base
     \<and> vmsz_aligned vptr ARMSection
     \<longrightarrow> ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots"
  by (simp add: less_kernel_base_mapping_slots)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> p) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> page_directory_at p s
        \<longrightarrow> p \<notin> global_refs s"
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply blast
  done

lemma cleanByVA_PoU_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> cleanByVA_PoU w q \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: cleanByVA_PoU_def machine_op_lift_def machine_rest_lift_def split_def | wp)+

lemma unmap_page_table_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vaddr < kernel_base
                     \<and> vmsz_aligned vaddr ARMSection)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (rule hoare_pre)
   apply (wp dmo_invs | wpc | simp)+
      apply (rule_tac Q="\<lambda>_. invs and K (asid \<le> mask asid_bits)" in hoare_post_imp)
       apply safe
        apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                   underlying_memory m p" in use_valid)
          apply ((wp | simp)+)[3]
       apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
   apply (wp store_pde_invs_unmap page_table_mapped_wp | wpc | simp)+
  apply (simp add: lookup_pd_slot_pd pde_ref_def)
  apply (strengthen lookup_pd_slot_kernel_mappings_strg
                    not_in_global_refs_vs_lookup)
  apply (auto simp: vspace_at_asid_def)
  done

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]

lemma mapM_x_swp_store_empty_table':
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt)
                 \<and> (\<forall>x. x \<in> (\<lambda>sl. ucast ((sl && mask pt_bits) >> 2)) ` set slots
                           \<or> pt x = InvalidPTE)) p
         and K (is_aligned p pt_bits \<and> (\<forall>x \<in> set slots. x && ~~ mask pt_bits = p))\<rbrace>
      mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct slots, simp_all add: mapM_x_Nil mapM_x_Cons)
   apply wp
   apply (clarsimp simp: obj_at_def empty_table_def fun_eq_iff)
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q)
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply auto
  done

lemma mapM_x_swp_store_empty_table:
  "\<lbrace>page_table_at p and pspace_aligned
       and K ((UNIV :: word8 set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pt_bits) >> 2)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pt_bits = p))\<rbrace>
     mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (wp mapM_x_swp_store_empty_table')
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm if_split_asm)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp: pt_bits_def pageBits_def)
  apply blast
  done

lemma pd_shifting_again:
  "\<lbrakk> is_aligned pd pd_bits \<rbrakk>
    \<Longrightarrow> pd + (ucast (ae :: 12 word) << 2) && ~~ mask pd_bits = pd"
  apply (erule add_mask_lower_bits)
  apply (clarsimp simp add: nth_shiftl nth_ucast word_size
                            pd_bits_def pageBits_def
                     dest!: test_bit_size)
  apply arith
  done

lemma pd_shifting_again2:
  "is_aligned (pd::word32) pd_bits \<Longrightarrow>
   pd + (ucast (ae::12 word) << 2) && mask pd_bits = (ucast ae << 2)"
  apply (rule conjunct1, erule is_aligned_add_helper)
  apply (rule ucast_less_shiftl_helper)
   apply (simp add: word_bits_def)
  apply (simp add: pd_bits_def pageBits_def)
  done

(* FIXME: move near Invariants_A.vs_lookup_2ConsD *)
lemma vs_lookup_pages_2ConsD:
  "((v # v' # vs) \<unrhd> p) s \<Longrightarrow>
   \<exists>p'. ((v' # vs) \<unrhd> p') s \<and> ((v' # vs, p') \<unrhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup_pages1_def)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_at:
  "[VSRef a None] \<rhd> pd = [VSRef a None] \<unrhd> pd"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_ap:
  "[VSRef b (Some AASIDPool), VSRef a None] \<rhd> pd =
   [VSRef b (Some AASIDPool), VSRef a None] \<unrhd> pd"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (erule rtranclE)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
    apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
    apply (fastforce simp: vs_refs_pages_def graph_of_def image_def
                          vs_lookup_pages1_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
   apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
   apply (fastforce simp: vs_refs_def graph_of_def image_def
                         vs_lookup1_def)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

lemma store_pde_unmap_pt:
  "\<lbrace>[VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd
        and K (is_aligned pd pd_bits)\<rbrace>
     store_pde (pd + (vaddr >> 20 << 2)) InvalidPDE
   \<lbrace>\<lambda>rv s.
        \<not> ([VSRef (vaddr >> 20) (Some APageDirectory),
            VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def
                 dest!: graph_ofD
                 split: if_split_asm
                        Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
    apply (simp add: pde_ref_def)
   apply (simp_all add: pd_shifting_again pd_shifting_again2
                        pd_casting_shifting word_size)
  apply (simp add: up_ucast_inj_eq)
  done

lemma vs_lookup_pages1_rtrancl_iterations:
  "(tup, tup') \<in> (vs_lookup_pages1 s)\<^sup>*
    \<Longrightarrow> (length (fst tup) \<le> length (fst tup')) \<and>
       (tup, tup') \<in> ((vs_lookup_pages1 s)
           ^^ (length (fst tup') - length (fst tup)))"
  apply (erule rtrancl_induct)
   apply simp
  apply (elim conjE)
  apply (subgoal_tac "length (fst z) = Suc (length (fst y))")
   apply (simp add: Suc_diff_le)
   apply (erule(1) relcompI)
  apply (clarsimp simp: vs_lookup_pages1_def)
  done

lemma store_pde_unmap_page:
  "\<lbrace>[VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd
        and K (is_aligned pd pd_bits)\<rbrace>
     store_pde (pd + (vaddr >> 20 << 2)) InvalidPDE
   \<lbrace>\<lambda>rv s.
        \<not> ([VSRef (vaddr >> 20) (Some APageDirectory),
            VSRef (asid && mask asid_low_bits) (Some AASIDPool),
            VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pde) s\<rbrace>"
  apply (simp add: store_pde_def vs_lookup_pages_eq_ap set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm
                        Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
    apply (simp add: pde_ref_pages_def)
   apply (simp_all add: pd_shifting_again pd_shifting_again2
                        pd_casting_shifting word_size)
  apply (simp add: up_ucast_inj_eq)
  done

(* FIXME: move to Invariants_A *)
lemma pte_ref_pages_invalid_None[simp]:
  "pte_ref_pages InvalidPTE = None"
  by (simp add: pte_ref_pages_def)

lemma store_pte_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (r \<unrhd> q) s\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. \<not> (r \<unrhd> q) s\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule swap, simp)
  apply (erule vs_lookup_pages_induct)
   apply (simp add: vs_lookup_pages_atI)
  apply (thin_tac "(ref \<unrhd> p) (kheap_update f s)" for ref p f)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                     graph_of_def image_def
              split: if_split_asm)

(* FIXME: move to Invariants_A *)
lemma pde_ref_pages_invalid_None[simp]:
  "pde_ref_pages InvalidPDE = None"
  by (simp add: pde_ref_pages_def)

lemma store_pde_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (r \<unrhd> q) s\<rbrace> store_pde p InvalidPDE \<lbrace>\<lambda>_ s. \<not> (r \<unrhd> q) s\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule swap, simp)
  apply (erule vs_lookup_pages_induct)
   apply (simp add: vs_lookup_pages_atI)
  apply (thin_tac "(ref \<unrhd> p) (kheap_update f s)" for ref p f)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                     graph_of_def image_def
              split: if_split_asm)

crunch vs_lookup_pages[wp]:
  get_hw_asid,find_pd_for_asid,set_vm_root_for_flush "\<lambda>s. P (vs_lookup_pages s)"

lemma flush_table_vs_lookup_pages[wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>
   flush_table a b c d
   \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  by (simp add: flush_table_def | wp mapM_UNIV_wp hoare_drop_imps | wpc
     | intro conjI impI)+

crunch vs_lookup_pages[wp]: page_table_mapped "\<lambda>s. P (vs_lookup_pages s)"

lemma unmap_page_table_unmapped[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s\<rbrace>"
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_pt page_table_mapped_wp | wpc | simp)+)[1]
  apply (clarsimp simp: vspace_at_asid_def pd_aligned pd_bits_def pageBits_def)
  done

lemma unmap_page_table_unmapped2:
  "\<lbrace>pspace_aligned and valid_vspace_objs and
      K (ref = [VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]
           \<and> p = pt)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> (ref \<rhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply simp
  apply wp
  done

lemma cacheRangeOp_lift[wp]:
  assumes o: "\<And>a b. \<lbrace>P\<rbrace> oper a b \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> cacheRangeOp oper x y z \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp: cacheRangeOp_def lineStart_def cacheLineBits_def cacheLine_def)
  apply (rule hoare_pre)
  apply (wp mapM_x_wp_inv o)
   apply (case_tac x, simp, wp o, simp)
  done

lemma cleanCacheRange_PoU_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> cleanCacheRange_PoU a b c \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: cleanCacheRange_PoU_def, wp)


lemma unmap_page_table_unmapped3:
  "\<lbrace>pspace_aligned and valid_vspace_objs and page_table_at pt and
      K (ref = [VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]
           \<and> p = pt)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_page | wpc | simp)+)[1]
   apply (rule page_table_mapped_wp)
  apply (clarsimp simp: vspace_at_asid_def pd_aligned pd_bits_def pageBits_def)
  apply (drule vs_lookup_pages_2ConsD)
  apply (clarsimp simp: obj_at_def vs_refs_pages_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (drule vs_lookup_pages_eq_ap[THEN fun_cong, symmetric, THEN iffD1])
  apply (erule swap)
  apply (drule (1) valid_vspace_objsD[rotated 2])
   apply (simp add: obj_at_def)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: obj_at_def vs_refs_def vs_lookup1_def
                        graph_of_def image_def
                 split: if_split_asm)
  apply (drule bspec, fastforce)
  apply (auto simp: obj_at_def data_at_def valid_pde_def pde_ref_def pde_ref_pages_def
                 split: pde.splits)
  done

lemma is_final_cap_caps_of_state_2D:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     is_final_cap' cap'' s; gen_obj_refs cap \<inter> gen_obj_refs cap'' \<noteq> {};
     gen_obj_refs cap' \<inter> gen_obj_refs cap'' \<noteq> {} \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (clarsimp simp: is_final_cap'_def3)
  apply (frule_tac x="fst p" in spec)
  apply (drule_tac x="snd p" in spec)
  apply (drule_tac x="fst p'" in spec)
  apply (drule_tac x="snd p'" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state Int_commute
                        prod_eqI)
  done

(* FIXME: move *)
lemma empty_table_pt_capI:
  "\<lbrakk>caps_of_state s p =
    Some (cap.ArchObjectCap (arch_cap.PageTableCap pt None));
    valid_table_caps s\<rbrakk>
   \<Longrightarrow> obj_at (empty_table (set (second_level_tables (arch_state s)))) pt s"
    apply (case_tac p)
    apply (clarsimp simp: valid_table_caps_def simp del: imp_disjL)
    apply (drule spec)+
    apply (erule impE, simp add: is_cap_simps)+
    by assumption

crunch underlying_memory[wp]: cleanCacheRange_PoC, cleanL2Range, invalidateL2Range, invalidateByVA,
                              cleanInvalidateL2Range, cleanInvalByVA, invalidateCacheRange_I,
                              branchFlushRange, ackInterrupt
                           "\<lambda>m'. underlying_memory m' p = um"
  (simp: cache_machine_op_defs machine_op_lift_def machine_rest_lift_def split_def)

crunch underlying_memory[wp]: cleanCacheRange_RAM, invalidateCacheRange_RAM,
                              cleanInvalidateCacheRange_RAM, do_flush
                "\<lambda>m'. underlying_memory m' p = um"
  (simp: crunch_simps)

lemma no_irq_do_flush:
  "no_irq (do_flush a b c d)"
  apply (simp add: do_flush_def)
  apply (case_tac a)
  apply (wp no_irq_dsb no_irq_invalidateCacheRange_I no_irq_branchFlushRange no_irq_isb | simp)+
  done

lemma cleanCacheRange_PoU_respects_device_region[wp]:
  "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> cleanCacheRange_PoU a b c \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  apply (clarsimp simp: cleanCacheRange_PoU_def cacheRangeOp_def)
  apply (wp mapM_x_wp |  wpc | clarsimp | fastforce)+
  done

lemma cacheRangeOp_respects_device_region[wp]:
  assumes valid_f: "\<And>a b P. \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> f a b \<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  shows "\<lbrace>\<lambda>ms. P (device_state ms)\<rbrace> cacheRangeOp f a b c\<lbrace>\<lambda>_ ms. P (device_state ms)\<rbrace>"
  apply (clarsimp simp: do_flush_def cacheRangeOp_def)
  apply (rule hoare_pre)
  apply (wp mapM_x_wp valid_f |  wpc | clarsimp | assumption)+
  done

crunches cleanByVA, cleanCacheRange_PoC, cleanCacheRange_RAM,
  cleanInvalByVA, invalidateByVA, invalidateL2Range,
  invalidateCacheRange_RAM, branchFlush, branchFlushRange,
  invalidateByVA_I, cleanInvalidateL2Range, do_flush, storeWord
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  (wp: cacheRangeOp_respects_device_region simp: crunch_simps)

crunch pspace_in_kernel_window[wp]: perform_page_invocation "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

crunch pspace_respects_device_region[wp]: perform_page_invocation "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region
         pspace_respects_device_region_dmo)

lemma perform_page_directory_invocation_invs[wp]:
  "\<lbrace>invs and valid_pdi pdi\<rbrace>
     perform_page_directory_invocation pdi
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pdi)
   apply (clarsimp simp: perform_page_directory_invocation_def)
   apply (wp dmo_invs set_vm_root_for_flush_invs
             hoare_vcg_const_imp_lift hoare_vcg_all_lift
          | simp)+
    apply (rule hoare_pre_imp[of _ \<top>], assumption)
    apply (clarsimp simp: valid_def)
    apply (thin_tac "p \<in> fst (set_vm_root_for_flush a b s)" for p a b)
    apply safe[1]
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
            in use_valid)
       apply ((clarsimp | wp)+)[3]
    apply(erule use_valid, wp no_irq_do_flush no_irq, assumption)
   apply(wp set_vm_root_for_flush_invs | simp add: valid_pdi_def)+
  apply (clarsimp simp: perform_page_directory_invocation_def)
  done

lemma perform_page_table_invocation_invs[wp]:
  notes no_irq[wp] hoare_pre [wp_pre del]
  shows
  "\<lbrace>invs and valid_pti pti\<rbrace>
   perform_page_table_invocation pti
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pti)
   apply (clarsimp simp: valid_pti_def perform_page_table_invocation_def)
   apply (wp dmo_invs)
    apply (rule_tac Q="\<lambda>_. invs" in hoare_post_imp)
     apply safe
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                underlying_memory m p" in use_valid)
       apply ((clarsimp simp: machine_op_lift_def
                             machine_rest_lift_def split_def | wp)+)[3]
     apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
    apply (wp store_pde_map_invs)[1]
   apply simp
   apply (rule hoare_pre, wp arch_update_cap_invs_map arch_update_cap_pspace
             arch_update_cap_valid_mdb set_cap_idle update_cap_ifunsafe
             valid_irq_node_typ valid_pde_lift set_cap_typ_at
             set_cap_irq_handlers set_cap_empty_pde
             hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift
             set_cap_arch_obj set_cap_obj_at_impossible set_cap_valid_arch_caps)
   apply (simp; intro conjI; clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_pt_cap_def is_arch_update_def cap_master_cap_def
                           vs_cap_ref_simps
                    split: cap.splits arch_cap.splits option.splits)
    apply fastforce
   apply (rule exI, rule conjI, assumption)
   apply (clarsimp simp: is_pt_cap_def is_arch_update_def
                         cap_master_cap_def cap_asid_def vs_cap_ref_simps
                         is_arch_cap_def pde_ref_def pde_ref_pages_def
                  split: cap.splits arch_cap.splits option.splits
                         pde.splits)
   apply (intro allI impI conjI, fastforce)
   apply (clarsimp simp: caps_of_def cap_of_def)
   apply (frule invs_pd_caps)
   apply (drule (1) empty_table_pt_capI)
   apply (clarsimp simp: obj_at_def empty_table_def pte_ref_pages_def)
  apply (clarsimp simp: perform_page_table_invocation_def
                 split: cap.split arch_cap.split)
  apply (rename_tac word option)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_invs_unmap_page_table get_cap_wp)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (wpc, wp, wpc)
   apply (rule hoare_lift_Pf2[where f=caps_of_state])
    apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift)+
        apply (rule hoare_vcg_conj_lift)
         apply (wp dmo_invs)
        apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                  valid_cap_typ[OF do_machine_op_obj_at]
                  mapM_x_swp_store_pte_invs[unfolded cte_wp_at_caps_of_state]
                  mapM_x_swp_store_empty_table
                  valid_cap_typ[OF unmap_page_table_typ_at]
                  unmap_page_table_unmapped3)+
        apply (rule hoare_pre_imp[of _ \<top>], assumption)
        apply (clarsimp simp: valid_def split_def)
        apply safe[1]
         apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                    underlying_memory m p" in use_valid)
         apply ((clarsimp | wp)+)[3]
               apply(erule use_valid, wp no_irq_cleanCacheRange_PoU, assumption)
       apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                 valid_cap_typ[OF do_machine_op_obj_at]
                 mapM_x_swp_store_pte_invs[unfolded cte_wp_at_caps_of_state]
                 mapM_x_swp_store_empty_table
                 valid_cap_typ[OF unmap_page_table_typ_at]
                 unmap_page_table_unmapped3 store_pte_no_lookup_pages
              | wp_once hoare_vcg_conj_lift
              | wp_once mapM_x_wp'
              | simp)+
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                        is_arch_diminished_def is_cap_simps
                        is_arch_update_def cap_rights_update_def
                        acap_rights_update_def cap_master_cap_simps
                        update_map_data_def)
  apply (frule (2) diminished_is_update')
  apply (simp add: cap_rights_update_def acap_rights_update_def)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (drule invs_pd_caps)
   apply (simp add: valid_table_caps_def)
   apply (elim allE, drule(1) mp)
   apply (simp add: is_cap_simps cap_asid_def)
   apply (drule mp, rule refl)
   apply (clarsimp simp: obj_at_def valid_cap_def empty_table_def
                         a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply (clarsimp simp: valid_cap_def mask_def[where n=asid_bits]
                        vmsz_aligned_def cap_aligned_def vs_cap_ref_def
                        invs_psp_aligned invs_vspace_objs)
  apply (subgoal_tac "(\<forall>x\<in>set [word , word + 4 .e. word + 2 ^ pt_bits - 1].
                             x && ~~ mask pt_bits = word)")
   apply (intro conjI)
      apply (simp add: cap_master_cap_def)
     apply fastforce
    apply (clarsimp simp: image_def)
    apply (subgoal_tac "word + (ucast x << 2)
                   \<in> set [word, word + 4 .e. word + 2 ^ pt_bits - 1]")
     apply (rule rev_bexI, assumption)
     apply (rule ccontr, erule more_pt_inner_beauty)
     apply simp
    apply (clarsimp simp: upto_enum_step_def linorder_not_less)
    apply (subst is_aligned_no_overflow,
           erule is_aligned_weaken,
           (simp_all add: pt_bits_def pageBits_def)[2])+
    apply (clarsimp simp: image_def word_shift_by_2)
    apply (rule exI, rule conjI[OF _ refl])
    apply (rule plus_one_helper)
    apply (rule order_less_le_trans, rule ucast_less, simp+)
  apply (clarsimp simp: upto_enum_step_def)
  apply (rule conjunct2, rule is_aligned_add_helper)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp only: word_shift_by_2)
  apply (rule shiftl_less_t2n)
   apply (rule minus_one_helper5)
    apply (simp add: pt_bits_def pageBits_def)+
  done

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at [wp]: unmap_page "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmap_page_typ_ats [wp] = abs_typ_at_lifts [OF unmap_page_typ_at]

lemma invalidateLocalTLB_VAASID_underlying_memory[wp]:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> invalidateLocalTLB_VAASID v \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: invalidateLocalTLB_VAASID_def machine_rest_lift_def machine_op_lift_def split_def | wp)+

lemma flush_page_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
  flush_page sz pd asid vptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: flush_page_def)
  apply (wp dmo_invs hoare_vcg_all_lift load_hw_asid_wp
            set_vm_root_for_flush_invs hoare_drop_imps
         | simp add: split_def)+
     apply (rule hoare_pre_imp[of _ \<top>], assumption)
     apply (clarsimp simp: valid_def)
     apply (thin_tac "x : fst (set_vm_root_for_flush a b c)" for x a b c)
     apply safe
      apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
             in use_valid)
        apply ((clarsimp | wp)+)[3]
       apply(erule use_valid, wp no_irq_invalidateLocalTLB_VAASID no_irq, assumption)
      apply (wp set_vm_root_for_flush_invs hoare_drop_imps|simp)+
  done

lemma find_pd_for_asid_lookup_slot [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace> find_pd_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (lookup_pd_slot rv vptr && ~~ mask pd_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule hoare_vcg_R_conj)
     apply (rule find_pd_for_asid_lookup)
    apply (rule find_pd_for_asid_aligned_pd)
   apply (simp add: pd_shifting lookup_pd_slot_def Let_def)
  apply simp
  done

lemma find_pd_for_asid_lookup_slot_large_page [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs and K (x \<in> set [0, 4 .e. 0x3C] \<and> is_aligned vptr 24)\<rbrace>
  find_pd_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (x + lookup_pd_slot rv vptr && ~~ mask pd_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule hoare_vcg_R_conj)
      apply (rule hoare_vcg_R_conj)
       apply (rule find_pd_for_asid_inv [where P="K (x \<in> set [0, 4 .e. 0x3C] \<and> is_aligned vptr 24)", THEN valid_validE_R])
     apply (rule find_pd_for_asid_lookup)
    apply (rule find_pd_for_asid_aligned_pd)
   apply (subst lookup_pd_slot_add_eq)
      apply (simp_all add: pd_bits_def pageBits_def)
  done

lemma find_pd_for_asid_pde_at_add [wp]:
 "\<lbrace>K (x \<in> set [0,4 .e. 0x3C] \<and> is_aligned vptr 24) and pspace_aligned and valid_vspace_objs\<rbrace>
  find_pd_for_asid asid \<lbrace>\<lambda>rv. pde_at (x + lookup_pd_slot rv vptr)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule hoare_vcg_R_conj)
     apply (rule find_pd_for_asid_inv [where P=
                 "K (x \<in> set [0, 4 .e. 0x3C] \<and> is_aligned vptr 24) and pspace_aligned", THEN valid_validE_R])
    apply (rule find_pd_for_asid_page_directory)
   apply (auto intro!: pde_at_aligned_vptr)
  done

lemma valid_kernel_mappingsD:
  "\<lbrakk> kheap s pdptr = Some (ArchObj (PageDirectory pd));
     valid_kernel_mappings s \<rbrakk>
      \<Longrightarrow> \<forall>x r. pde_ref (pd x) = Some r \<longrightarrow>
                  (r \<in> set (arm_global_pts (arch_state s)))
                       = (ucast (kernel_base >> 20) \<le> x)"
  apply (simp add: valid_kernel_mappings_def)
  apply (drule bspec, erule ranI)
  apply (simp add: valid_kernel_mappings_if_pd_def
                   kernel_mapping_slots_def)
  done

lemma lookup_pt_slot_cap_to:
  shows "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)\<rbrace> lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> is_pt_cap cap
                                \<and> rv && ~~ mask pt_bits \<in> obj_refs cap
                                \<and>  s \<turnstile> cap \<and> cap_asid cap \<noteq> None
                                \<and> (is_aligned vptr 16 \<longrightarrow> is_aligned rv 6)\<rbrace>, -"
  proof -
    have shift: "(2::word32) ^ pt_bits = 2 ^ 8 << 2"
      by (simp add:pt_bits_def pageBits_def )
  show ?thesis
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply (frule(1) valid_vspace_objsD)
   apply fastforce
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I[OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule pde_graph_ofI)
     apply (erule (1) less_kernel_base_mapping_slots)
    apply (simp add: pde_ref_def)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply simp
  apply (elim exEI, clarsimp)
  apply (subst is_aligned_add_helper[THEN conjunct2])
    apply (drule caps_of_state_valid)
     apply fastforce
    apply (clarsimp dest!:valid_cap_aligned simp:cap_aligned_def vs_cap_ref_def
      obj_refs_def obj_ref_of_def pageBitsForSize_def pt_bits_def pageBits_def
      elim!:is_aligned_weaken
      split:arch_cap.split_asm cap.splits option.split_asm vmpage_size.split_asm)
   apply (rule less_le_trans[OF shiftl_less_t2n[where m = 10]])
     apply (rule le_less_trans[OF word_and_le1])
     apply simp
    apply simp
   apply (simp add:pt_bits_def pageBits_def)
  apply (drule caps_of_state_valid)
   apply fastforce
  apply (drule bspec)
   apply (drule(1) less_kernel_base_mapping_slots)
   apply simp
  apply (clarsimp simp: valid_pde_def obj_at_def
                        vs_cap_ref_def is_pt_cap_def valid_cap_simps cap_aligned_def
                 split: cap.split_asm arch_cap.split_asm vmpage_size.splits
                        option.split_asm if_splits)
    apply (erule is_aligned_add[OF is_aligned_weaken],simp
      ,rule is_aligned_shiftl[OF is_aligned_andI1,OF is_aligned_shiftr],simp)+
  done
qed

lemma lookup_pt_slot_cap_to1[wp]:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)\<rbrace> lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> is_pt_cap cap \<and> rv && ~~ mask pt_bits \<in> obj_refs cap\<rbrace>,-"
  apply (rule hoare_post_imp_R)
   apply (rule lookup_pt_slot_cap_to)
  apply auto
  done

lemma lookup_pt_slot_cap_to_multiple1:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)
                  and K (is_aligned vptr 16)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. is_aligned rv 6 \<and>
             (\<exists>a b. cte_wp_at (\<lambda>c. is_pt_cap c \<and> cap_asid c \<noteq> None
                                  \<and> (\<lambda>x. x && ~~ mask pt_bits) ` set [rv , rv + 4 .e. rv + 0x3C] \<subseteq> obj_refs c) (a, b) s)\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (rule hoare_post_imp_R)
   apply (rule lookup_pt_slot_cap_to)
  apply (rule conjI, clarsimp)
  apply (elim exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_pt_cap_def
                        valid_cap_def cap_aligned_def
                   del: subsetI)
  apply (simp add: subset_eq p_0x3C_shift)
  apply (clarsimp simp: set_upto_enum_step_4)
  apply (fold mask_def[where n=4, simplified])
  apply (subst(asm) le_mask_iff)
  apply (subst word_plus_and_or_coroll)
   apply (rule shiftr_eqD[where n=6])
     apply (simp add: shiftr_over_and_dist shiftl_shiftr2)
    apply (simp add: is_aligned_andI2)
   apply simp
  apply (simp add: word_ao_dist)
  apply (simp add: and_not_mask pt_bits_def pageBits_def)
  apply (drule arg_cong[where f="\<lambda>x. x >> 4"])
  apply (simp add: shiftl_shiftr2 shiftr_shiftr)
  done

lemma lookup_pt_slot_cap_to_multiple[wp]:
  "\<lbrace>invs and \<exists>\<rhd>pd and K (is_aligned pd pd_bits)
                  and K (vptr < kernel_base)
                  and K (is_aligned vptr 16)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>a b. cte_wp_at (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` (\<lambda>x. x + rv) ` set [0 , 4 .e. 0x3C] \<subseteq> obj_refs c) (a, b) s\<rbrace>, -"
  apply (rule hoare_post_imp_R, rule lookup_pt_slot_cap_to_multiple1)
  apply (elim conjE exEI cte_wp_at_weakenE)
  apply (simp add: subset_eq p_0x3C_shift)
  done

lemma find_pd_for_asid_cap_to:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> rv \<in> obj_refs cap
                                \<and> is_pd_cap cap \<and> s \<turnstile> cap
                                \<and> is_aligned rv pd_bits\<rbrace>, -"
  apply (simp add: find_pd_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (frule(1) valid_vspace_objsD, clarsimp)
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I [OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule graph_ofI)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (simp, elim exEI)
  apply clarsimp
  apply (frule caps_of_state_valid_cap, clarsimp+)
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric] table_cap_ref_def
                        is_pd_cap_def valid_cap_def cap_aligned_def
                        pd_bits_def pageBits_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  done

lemma find_pd_for_asid_cap_to1[wp]:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> lookup_pd_slot rv vptr && ~~ mask pd_bits \<in> obj_refs cap\<rbrace>, -"
  apply (rule hoare_post_imp_R, rule find_pd_for_asid_cap_to)
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply auto
  done

lemma find_pd_for_asid_cap_to2[wp]:
  "\<lbrace>invs\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>a b. cte_wp_at
            (\<lambda>cp. lookup_pd_slot rv vptr && ~~ mask pd_bits \<in> obj_refs cp \<and> is_pd_cap cp)
                  (a, b) s\<rbrace>, -"
  apply (rule hoare_post_imp_R, rule find_pd_for_asid_cap_to)
  apply (clarsimp simp: lookup_pd_slot_pd cte_wp_at_caps_of_state)
  apply auto
  done

lemma find_pd_for_asid_cap_to_multiple[wp]:
  "\<lbrace>invs and K (is_aligned vptr 24)\<rbrace> find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<exists>x xa. cte_wp_at (\<lambda>a. (\<lambda>x. x && ~~ mask pd_bits) ` (\<lambda>x. x + lookup_pd_slot rv vptr) ` set [0 , 4 .e. 0x3C] \<subseteq> obj_refs a) (x, xa) s\<rbrace>, -"
  apply (rule hoare_gen_asmE, rule hoare_post_imp_R, rule find_pd_for_asid_cap_to)
  apply (elim exEI, clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: lookup_pd_slot_add_eq)
  done

lemma find_pd_for_asid_cap_to_multiple2[wp]:
  "\<lbrace>invs and K (is_aligned vptr 24)\<rbrace>
     find_pd_for_asid asid
   \<lbrace>\<lambda>rv s. \<forall>x\<in>set [0 , 4 .e. 0x3C]. \<exists>a b.
             cte_wp_at (\<lambda>cp. x + lookup_pd_slot rv vptr && ~~ mask pd_bits
                             \<in> obj_refs cp \<and> is_pd_cap cp) (a, b) s\<rbrace>, -"
  apply (rule hoare_gen_asmE, rule hoare_post_imp_R,
         rule find_pd_for_asid_cap_to)
  apply (intro ballI, elim exEI,
         clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: lookup_pd_slot_add_eq)
  done

lemma unat_ucast_kernel_base_rshift:
  "unat (ucast (kernel_base >> 20) :: 12 word)
     = unat (kernel_base >> 20)"
  by (simp add: kernel_base_def)

lemma lookup_pd_slot_kernel_mappings_set_strg:
  "is_aligned pd pd_bits \<and> vmsz_aligned vptr ARMSuperSection
     \<and> vptr < kernel_base
          \<longrightarrow>
   (\<forall>x\<in>set [0 , 4 .e. 0x3C]. ucast (x + lookup_pd_slot pd vptr && mask pd_bits >> 2)
            \<notin> kernel_mapping_slots)"
  apply (clarsimp simp: upto_enum_step_def word_shift_by_2)
  apply (simp add: less_kernel_base_mapping_slots_both minus_one_helper5)
  done

lemma lookup_pt_slot_cap_to2:
  "\<lbrace>invs and \<exists>\<rhd> pd and K (is_aligned pd pd_bits) and K (vptr < kernel_base)\<rbrace>
     lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>oref cref cap. caps_of_state s (oref, cref) = Some cap
         \<and> rv && ~~ mask pt_bits \<in> obj_refs cap \<and> is_pt_cap cap\<rbrace>, -"
  apply (rule hoare_post_imp_R, rule lookup_pt_slot_cap_to)
  apply fastforce
  done

lemma lookup_pt_slot_cap_to_multiple2:
  "\<lbrace>invs and \<exists>\<rhd> pd and K (is_aligned pd pd_bits) and K (vptr < kernel_base) and K (is_aligned vptr 16)\<rbrace>
      lookup_pt_slot pd vptr
   \<lbrace>\<lambda>rv s. \<exists>oref cref. cte_wp_at
              (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` (\<lambda>x. x + rv) ` set [0 , 4 .e. 0x3C] \<subseteq> obj_refs c \<and> is_pt_cap c)
                  (oref, cref) s\<rbrace>, -"
  apply (rule hoare_post_imp_R, rule lookup_pt_slot_cap_to_multiple1)
  apply (clarsimp simp: upto_enum_step_def image_image field_simps
                        linorder_not_le[symmetric]
                 split: if_split_asm)
   apply (erule notE, erule is_aligned_no_wrap')
   apply simp
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done

crunch global_refs[wp]: flush_page "\<lambda>s. P (global_refs s)"
  (simp: global_refs_arch_update_eq crunch_simps)

lemma page_directory_at_lookup_mask_aligned_strg:
  "is_aligned pd pd_bits \<and> page_directory_at pd s
      \<longrightarrow> page_directory_at (lookup_pd_slot pd vptr && ~~ mask pd_bits) s"
  by (clarsimp simp: lookup_pd_slot_pd)

lemma page_directory_at_lookup_mask_add_aligned_strg:
  "is_aligned pd pd_bits \<and> page_directory_at pd s
               \<and> vmsz_aligned vptr ARMSuperSection
               \<and> x \<in> set [0, 4 .e. 0x3C]
      \<longrightarrow> page_directory_at (x + lookup_pd_slot pd vptr && ~~ mask pd_bits) s"
  by (clarsimp simp: lookup_pd_slot_add_eq vmsz_aligned_def)

lemma dmo_ccMVA_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (cleanByVA_PoU a b) \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp | wp)+)[3]
  apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
  done


lemma dmo_ccr_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (cleanCacheRange_PoU a b c) \<lbrace>\<lambda>r. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp | wp)+)[3]
  apply(erule use_valid, wp no_irq_cleanCacheRange_PoU no_irq, assumption)
  done

(* FIXME: move to Invariants_A *)
lemmas pte_ref_pages_simps[simp] =
       pte_ref_pages_def[split_simps pte.split]

lemma ex_pt_cap_eq:
  "(\<exists>ref cap. caps_of_state s ref = Some cap \<and>
              p \<in> obj_refs cap \<and> is_pt_cap cap) =
   (\<exists>ref asid. caps_of_state s ref =
               Some (cap.ArchObjectCap (arch_cap.PageTableCap p asid)))"
  by (fastforce simp add: is_pt_cap_def obj_refs_def)

lemmas lookup_pt_slot_cap_to2' =
  lookup_pt_slot_cap_to2[simplified ex_pt_cap_eq[simplified split_paired_Ex]]

lemma unmap_page_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vptr < kernel_base \<and>
                vmsz_aligned vptr sz)\<rbrace>
      unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_def)
  apply (rule hoare_pre)
   apply (wp flush_page_invs hoare_vcg_const_imp_lift)
    apply (wp hoare_drop_imp[where f="check_mapping_pptr a b c" for a b c]
              hoare_drop_impE_R[where R="\<lambda>x y. x && mask b = c" for b c]
              lookup_pt_slot_inv lookup_pt_slot_cap_to2'
              lookup_pt_slot_cap_to_multiple2
              store_pde_invs_unmap mapM_swp_store_pde_invs_unmap
              mapM_swp_store_pte_invs
           | wpc | simp)+
   apply (strengthen lookup_pd_slot_kernel_mappings_strg
                     lookup_pd_slot_kernel_mappings_set_strg
                     not_in_global_refs_vs_lookup
                     page_directory_at_lookup_mask_aligned_strg
                     page_directory_at_lookup_mask_add_aligned_strg)+
   apply (wp find_pd_for_asid_page_directory
             hoare_vcg_const_imp_lift_R hoare_vcg_const_Ball_lift_R
          | wp_once hoare_drop_imps)+
  apply (auto simp: vmsz_aligned_def)
  done

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma "\<lbrace>\<lambda>s. P (vs_lookup s) (valid_pte pte s)\<rbrace> set_cap cap cptr \<lbrace>\<lambda>_ s. P (vs_lookup s) (valid_pte pte s)\<rbrace>"
  apply (rule hoare_lift_Pf[where f=vs_lookup])
  apply (rule hoare_lift_Pf[where f="valid_pte pte"])
    apply (wp set_cap.vs_lookup set_cap_valid_pte_stronger)+
  done

lemma reachable_page_table_not_global:
  "\<lbrakk>(ref \<rhd> p) s; valid_kernel_mappings s; valid_global_pts s;
    valid_vspace_objs s; valid_asid_table (arm_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> p \<notin> set (arm_global_pts (arch_state s))"
  apply clarsimp
  apply (erule (2) vs_lookupE_alt[OF _ _ valid_asid_table_ran])
    apply (clarsimp simp: valid_global_pts_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp simp: valid_global_pts_def)
   apply (drule (1) bspec)
   apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pd_def ran_def)
  apply (drule_tac x="ArchObj (PageDirectory pd)" in spec)
  apply (drule mp, erule_tac x=p\<^sub>2 in exI)
  apply clarsimp
  done

lemma store_pte_unmap_page:
  "\<lbrace>(\<lambda>s. \<exists>pt. ([VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pt) s
     \<and> is_aligned pt pt_bits \<and> p = (pt + ((vaddr >> 12) && mask 8 << 2 )))\<rbrace>
     store_pte p InvalidPTE
   \<lbrace>\<lambda>rv s.\<not> ([VSRef ((vaddr >> 12) && mask 8) (Some APageTable),
             VSRef (vaddr >> 20) (Some APageDirectory),
             VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pptr) s\<rbrace>"
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric] vs_lookup_pages_def vs_asid_refs_def)
  apply (drule vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def vs_lookup_def vs_asid_refs_def)
  apply (drule vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def split: if_split_asm)
         apply (clarsimp simp: vs_refs_pages_def)+
      apply (thin_tac "(VSRef a (Some AASIDPool), b) \<in> c" for a b c)
      apply (clarsimp simp: graph_of_def
                     split: Structures_A.kernel_object.split_asm
                            arch_kernel_obj.splits
                            if_split_asm)
      apply (erule_tac P="a = c" for c in swap)
      apply (rule up_ucast_inj[where 'a=8 and 'b=32])
       apply (subst ucast_ucast_len)
        apply (simp add: pt_bits_def pageBits_def
                         is_aligned_add_helper less_le_trans[OF ucast_less]
                         shiftl_less_t2n'[where m=8 and n=2, simplified]
                         shiftr_less_t2n'[where m=8 and n=2, simplified]
                         word_bits_def shiftl_shiftr_id)+
     apply (clarsimp simp: graph_of_def vs_refs_def vs_refs_pages_def
                          pde_ref_def pde_ref_pages_def pte_ref_pages_def)+
  apply (simp add: pt_bits_def pageBits_def
                   is_aligned_add_helper less_le_trans[OF ucast_less]
                   shiftl_less_t2n'[where m=8 and n=2, simplified]
                   shiftr_less_t2n'[where m=8 and n=2, simplified]
                   word_bits_def shiftl_shiftr_id)+
  by (clarsimp   split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm,
         clarsimp simp: pde_ref_def pte_ref_pages_def pde_ref_pages_def data_at_def
                        is_aligned_add_helper less_le_trans[OF ucast_less]
                        shiftl_less_t2n'[where m=8 and n=2, simplified]
                 dest!: graph_ofD ucast_up_inj[where 'a=10 (*asid_low_bits*)and 'b=32, simplified]
                        ucast_up_inj[where 'a=7 (*asid_high_bits*) and 'b=32, simplified]
                 split: if_split_asm  pde.splits pte.splits if_splits)

crunch pd_at: flush_page "\<lambda>s. P (ko_at (ArchObj (PageDirectory pd)) x s)"
  (wp: crunch_wps simp: crunch_simps)

crunch pt_at: flush_page "\<lambda>s. P (ko_at (ArchObj (PageTable pt)) x s)"
  (wp: crunch_wps simp: crunch_simps)

lemma vs_lookup_pages_pteD:
  "([VSRef ((vaddr >> 12) && mask 8) (Some APageTable),
     VSRef (vaddr >> 20) (Some APageDirectory),
     VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pg) s
   \<Longrightarrow>  \<exists>ap fun pd funa pt funb. ([VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> ap) s
               \<and> (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pd) s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd
               \<and> ko_at (ArchObj (PageDirectory funa)) pd s
               \<and> ([VSRef (vaddr >> 20) (Some APageDirectory),
                  VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pt) s
               \<and> pde_ref_pages (funa (ucast (vaddr >> 20))) = Some pt
               \<and> ko_at (ArchObj (PageTable funb)) pt s
               \<and> pte_ref_pages (funb (ucast ((vaddr >> 12) && mask 8 ))) = Some pg"

  apply (frule vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[z]" for z in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[]" in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (rule_tac x=p'b in exI)
  apply (frule vs_lookup_atD[OF iffD2[OF fun_cong[OF vs_lookup_pages_eq_at]]])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_mapping_slots_def kernel_base_def
                   not_le ucast_less_ucast[symmetric, where 'a=12 and 'b=32]
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def pte_ref_pages_def
            split: if_split_asm)
  apply (simp add: ucast_ucast_id
            split: pde.split_asm pte.split_asm)
  done

lemma vs_lookup_pages_pdeD:
  "([VSRef (vaddr >> 20) (Some APageDirectory),
     VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s
   \<Longrightarrow>  \<exists>ap fun pd funa. ([VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> ap) s
               \<and> (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                  VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pd) s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd
               \<and> ko_at (ArchObj (PageDirectory funa)) pd s
               \<and> pde_ref_pages (funa (ucast (vaddr >> 20))) = Some p"

  apply (frule vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (frule_tac vs="[]" in vs_lookup_pages_2ConsD)
  apply clarsimp
  apply (rule_tac x=p'a in exI)
  apply (frule vs_lookup_atD[OF iffD2[OF fun_cong[OF vs_lookup_pages_eq_at]]])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_mapping_slots_def kernel_base_def
                   not_le ucast_less_ucast[symmetric, where 'a=12 and 'b=32]
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def
            split: if_split_asm)
  apply (simp add: ucast_ucast_id
            split: pde.split_asm)
  done

lemma vs_lookup_ap_mappingD:
  "([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
     VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd) s
   \<Longrightarrow> \<exists>ap fun. (arm_asid_table (arch_state s)) (asid_high_bits_of asid) = Some ap
               \<and> ko_at (ArchObj (ASIDPool fun)) ap s
               \<and> fun (ucast (asid && mask asid_low_bits)) = Some pd"
apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)
  apply (simp add: up_ucast_inj_eq graph_of_def kernel_mapping_slots_def kernel_base_def
                   not_le ucast_less_ucast[symmetric, where 'a=12 and 'b=32]
                   mask_asid_low_bits_ucast_ucast pde_ref_pages_def pte_ref_pages_def
            split: if_split_asm)
  done

lemma kernel_slot_impossible_vs_lookup_pages:
  "(ucast (vaddr >> 20)) \<in> kernel_mapping_slots \<Longrightarrow>
   \<not> ([VSRef ((vaddr >> 12) && mask 8) (Some APageTable),
       VSRef (vaddr >> 20) (Some APageDirectory),
       VSRef (asid && mask asid_low_bits) (Some AASIDPool),
       VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pptr) s"
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def)
  apply (clarsimp simp: ucast_ucast_id
                 dest!: graph_ofD
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                        if_split_asm)
  done

lemma kernel_slot_impossible_vs_lookup_pages2:
  "(ucast (vaddr >> 20)) \<in> kernel_mapping_slots \<Longrightarrow>
   \<not> ([VSRef (vaddr >> 20) (Some APageDirectory),
       VSRef (asid && mask asid_low_bits) (Some AASIDPool),
       VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> pptr) s"
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: vs_lookup_pages1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def)
  apply (clarsimp simp: ucast_ucast_id
                 dest!: graph_ofD
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                        if_split_asm)
  done

lemma pt_aligned:
  "\<lbrakk>page_table_at pt s; pspace_aligned s\<rbrakk>
   \<Longrightarrow> is_aligned pt 10"
  by (auto simp: obj_at_def pspace_aligned_def pt_bits_def pageBits_def dom_def)

lemma vaddr_segment_nonsense:
  "is_aligned (p :: word32) 14 \<Longrightarrow>
   p + (vaddr >> 20 << 2) && ~~ mask pd_bits = p"
  by (simp add: mask_32_max_word
    shiftl_less_t2n'[where m=12 and n=2, simplified]
    shiftr_less_t2n'[where m=12 and n=20, simplified]
    pd_bits_def pageBits_def
    is_aligned_add_helper[THEN conjunct2])

lemma vaddr_segment_nonsense2:
  "is_aligned (p :: word32) 14 \<Longrightarrow>
   p + (vaddr >> 20 << 2) && mask pd_bits >> 2 = vaddr >> 20"
  by (simp add: mask_32_max_word
    shiftl_less_t2n'[where m=12 and n=2, simplified]
    shiftr_less_t2n'[where m=12 and n=20, simplified]
    pd_bits_def pageBits_def
    is_aligned_add_helper[THEN conjunct1]
    triple_shift_fun)

lemma vaddr_segment_nonsense3:
  "is_aligned (p :: word32) 10 \<Longrightarrow>
   (p + ((vaddr >> 12) && 0xFF << 2) && ~~ mask pt_bits) = p"
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (simp add: pt_bits_def pageBits_def)+
  apply (rule shiftl_less_t2n[where m=10 and n=2, simplified, OF and_mask_less'[where n=8, unfolded mask_def, simplified]])
   apply simp+
  done

lemma vaddr_segment_nonsense4:
  "is_aligned (p :: word32) 10 \<Longrightarrow>
   p + ((vaddr >> 12) && 0xFF << 2) && mask pt_bits = (vaddr >> 12) && 0xFF << 2"
  apply (subst is_aligned_add_helper[THEN conjunct1])
    apply (simp_all add: pt_bits_def pageBits_def)
   apply (rule shiftl_less_t2n'[where n=2 and m=8, simplified])
    apply (rule and_mask_less'[where n=8, unfolded mask_def, simplified])
    apply simp+
  done

(* FIXME: move near ArchAcc_R.lookup_pt_slot_inv? *)
lemma lookup_pt_slot_inv_validE:
  "\<lbrace>P\<rbrace> lookup_pt_slot pd vptr \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: lookup_pt_slot_def)
  apply (wp get_pde_inv hoare_drop_imp lookup_pt_slot_inv | wpc | simp)+
  done

lemma unmap_page_no_lookup_pages:
  "\<lbrace>\<lambda>s. \<not> (ref \<unrhd> p) s\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>_ s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_pre)
  apply (wp store_pte_no_lookup_pages hoare_drop_imps lookup_pt_slot_inv_validE
         mapM_UNIV_wp store_pde_no_lookup_pages
      | wpc | simp add: unmap_page_def swp_def | strengthen imp_consequent)+
  done

lemma vs_refs_pages_inj:
  "\<lbrakk> (r, p) \<in> vs_refs_pages ko; (r, p') \<in> vs_refs_pages ko \<rbrakk> \<Longrightarrow> p = p'"
  by (clarsimp simp: vs_refs_pages_def up_ucast_inj_eq dest!: graph_ofD
              split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits)

lemma unique_vs_lookup_pages_loop:
  "\<lbrakk> (([r], x), a # list, p) \<in> vs_lookup_pages1 s ^^ length list;
      (([r'], y), a # list, p') \<in> vs_lookup_pages1 s ^^ length list;
      r = r' \<longrightarrow> x = y \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (induct list arbitrary: a p p')
   apply simp
  apply (clarsimp simp: obj_at_def dest!: vs_lookup_pages1D)
  apply (erule vs_refs_pages_inj)
  apply fastforce
  done

lemma unique_vs_lookup_pages:
  "\<lbrakk>(r \<unrhd> p) s; (r \<unrhd> p') s\<rbrakk> \<Longrightarrow> p = p'"
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_pages1_rtrancl_iterations)
  apply (case_tac r, simp_all)
  apply (erule(1) unique_vs_lookup_pages_loop)
  apply (clarsimp simp: up_ucast_inj_eq)
  done

lemma unmap_page_unmapped:
  "\<lbrace>pspace_aligned and valid_vspace_objs and data_at sz pptr and
    valid_objs and (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    K ((sz = ARMSmallPage \<or> sz = ARMLargePage \<longrightarrow> ref =
              [VSRef ((vaddr >> 12) && mask 8) (Some APageTable),
               VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
       (sz = ARMSection \<or> sz = ARMSuperSection \<longrightarrow> ref =
              [VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
        p = pptr)\<rbrace>
  unmap_page sz asid vaddr pptr
  \<lbrace>\<lambda>rv s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm)

    (* Establish that pptr reachable, otherwise trivial *)
  apply (rule hoare_name_pre_state2)
  apply (case_tac "\<not> (ref \<unrhd> p) s")
   apply (rule hoare_pre(1)[OF unmap_page_no_lookup_pages])
   apply clarsimp+

     (* This should be somewhere else but isn't *)
  apply (subgoal_tac "\<exists>xs. [0 :: word32, 4 .e. 0x3C] = 0 # xs")
   prefer 2
   apply (simp add: upto_enum_step_def upto_enum_word upt_rec)
  apply (clarsimp simp: unmap_page_def lookup_pd_slot_def lookup_pt_slot_def Let_def
                        mapM_Cons
                  cong: option.case_cong vmpage_size.case_cong)

    (* Establish that pde in vsref chain isn't kernel mapping,
       otherwise trivial *)
  apply (case_tac "ucast (vaddr >> 20) \<in> kernel_mapping_slots")
   apply (case_tac sz)
       apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages | wp)+)[2]
     apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]
    apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]

      (* Proper cases *)
  apply (wp store_pte_unmap_page
            mapM_UNIV_wp[OF store_pte_no_lookup_pages]
            get_pte_wp get_pde_wp store_pde_unmap_page
            mapM_UNIV_wp[OF store_pde_no_lookup_pages]
            flush_page_vs_lookup flush_page_vs_lookup_pages
            hoare_vcg_all_lift hoare_vcg_const_imp_lift
            hoare_vcg_imp_lift[OF flush_page_pd_at]
            hoare_vcg_imp_lift[OF flush_page_pt_at]
            find_pd_for_asid_lots
         | wpc | simp add: swp_def check_mapping_pptr_def)+
  apply clarsimp
  apply (case_tac sz, simp_all)
     apply (drule vs_lookup_pages_pteD)
     apply (rule conjI[rotated])
      apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
     apply clarsimp
     apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
     apply (frule (1) pd_aligned)
     apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
     apply (frule valid_vspace_objsD)
       apply (clarsimp simp: obj_at_def a_type_def)
       apply (rule refl)
      apply assumption
     apply (simp, drule bspec, fastforce)
     apply (clarsimp simp: pde_ref_pages_def
                    split: pde.splits
                    dest!: )
       apply (frule pt_aligned[rotated])
        apply (simp add: obj_at_def a_type_def)
        apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
       apply (clarsimp simp: obj_at_def)
       apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr]
                        vaddr_segment_nonsense4[where vaddr=vaddr])
       apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
          apply ((simp add: obj_at_def a_type_def)+)[3]
       apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
         apply ((simp add: obj_at_def)+)[2]
       apply (simp add: )
       apply (intro conjI impI)
        apply (simp add: pt_bits_def pageBits_def mask_def)
       apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 8))"])
       apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                             shiftl_shiftr_id[where n=2,
                                             OF _ less_le_trans[OF and_mask_less'[where n=8]],
                                             unfolded mask_def word_bits_def, simplified]
                      split: pte.splits if_splits)
      apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]

    apply (drule vs_lookup_pages_pteD)
    apply (rule conjI[rotated])
     apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
    apply clarsimp
    apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
    apply (frule (1) pd_aligned)
    apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
    apply (frule valid_vspace_objsD)
      apply (clarsimp simp: obj_at_def a_type_def)
      apply (rule refl)
     apply assumption
    apply (simp, drule bspec, fastforce)
    apply (clarsimp simp: pde_ref_pages_def
                   split: pde.splits
                   dest!: )
      apply (frule pt_aligned[rotated])
       apply (simp add: obj_at_def a_type_def)
       apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
      apply (clarsimp simp: obj_at_def)
      apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr]
                       vaddr_segment_nonsense4[where vaddr=vaddr])
      apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
         apply ((simp add: obj_at_def a_type_def)+)[3]
      apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
        apply ((simp add: obj_at_def)+)[2]
      apply (simp add: )
      apply (intro conjI impI)
       apply (simp add: pt_bits_def pageBits_def mask_def)
      apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 8))"])

       apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                             shiftl_shiftr_id[where n=2,
                                             OF _ less_le_trans[OF and_mask_less'[where n=8]],
                                             unfolded mask_def word_bits_def, simplified]
                      split: pte.splits if_splits)
      apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]
   apply (drule vs_lookup_pages_pdeD)
   apply (rule conjI[rotated])
    apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
   apply clarsimp
   apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
   apply (frule (1) pd_aligned)
   apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
   apply (frule valid_vspace_objsD)
     apply (clarsimp simp: obj_at_def a_type_def)
     apply (rule refl)
    apply assumption
   apply (simp, drule bspec, fastforce)
   apply (clarsimp simp: pde_ref_pages_def
                  split: pde.splits)
     apply (clarsimp simp: obj_at_def data_at_def)
    apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
       apply ((simp add: obj_at_def a_type_def)+)[3]
    apply (frule_tac p="rv" in valid_vspace_objsD)
      apply ((simp add: obj_at_def)+)[2]
    apply (fastforce simp: data_at_def)
   apply (fastforce simp: obj_at_def a_type_def pd_bits_def pageBits_def data_at_def
                   split: pde.splits)
   apply (fastforce simp: obj_at_def a_type_def data_at_def)

  apply (drule vs_lookup_pages_pdeD)
  apply (rule conjI[rotated])
   apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
  apply clarsimp
  apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
  apply (frule (1) pd_aligned)
  apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
  apply (frule valid_vspace_objsD)
    apply (clarsimp simp: obj_at_def a_type_def)
    apply (rule refl)
   apply assumption
  apply (simp, drule bspec, fastforce)
  apply (clarsimp simp: pde_ref_pages_def
                 split: pde.splits)
    apply (fastforce simp: obj_at_def data_at_def)
   apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
      apply ((simp add: obj_at_def a_type_def)+)[3]
   apply (frule_tac p="rv" in valid_vspace_objsD)
     apply ((simp add: obj_at_def)+)[2]
   apply (simp add: )
   apply (drule bspec[where x="ucast (vaddr >> 20)"], simp)
   apply (fastforce simp: obj_at_def a_type_def pd_bits_def pageBits_def data_at_def
                  split: pde.splits)
  apply (clarsimp simp: obj_at_def a_type_def pd_bits_def pageBits_def)
  done

lemma unmap_page_page_unmapped:
  "\<lbrace>pspace_aligned and valid_objs and valid_vspace_objs and
    (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    data_at sz pptr and
    K (p = pptr) and K (sz = ARMSmallPage \<or> sz = ARMLargePage)\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef ((vaddr >> 12) && mask 8) (Some APageTable),
               VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s\<rbrace>"
  by (rule hoare_pre_imp[OF _ unmap_page_unmapped]) auto

lemma unmap_page_section_unmapped:
  "\<lbrace>pspace_aligned and valid_objs and valid_vspace_objs and
    (\<lambda>s. valid_asid_table (arm_asid_table (arch_state s)) s) and
    data_at sz pptr and
    K (p = pptr) and K (sz = ARMSection \<or> sz = ARMSuperSection)\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (vaddr >> 20) (Some APageDirectory),
               VSRef (asid && mask asid_low_bits) (Some AASIDPool),
               VSRef (ucast (asid_high_bits_of asid)) None] \<unrhd> p) s\<rbrace>"
  by (rule hoare_pre_imp[OF _ unmap_page_unmapped]) auto

crunch global_refs: store_pde "\<lambda>s. P (global_refs s)"

crunch invs[wp]: pte_check_if_mapped, pde_check_if_mapped "invs"

crunch vs_lookup[wp]: pte_check_if_mapped, pde_check_if_mapped "\<lambda>s. P (vs_lookup s)"

crunch valid_pte[wp]: pte_check_if_mapped "\<lambda>s. P (valid_pte p s)"

lemma set_mi_invs[wp]: "\<lbrace>invs\<rbrace> set_message_info t a \<lbrace>\<lambda>x. invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma data_at_orth:
  "data_at a p s \<Longrightarrow> \<not> ep_at p s
  \<and> \<not> ntfn_at p s \<and>\<not> cap_table_at sz p s \<and> \<not> tcb_at p s \<and> \<not> asid_pool_at p s
  \<and> \<not> page_table_at p s \<and> \<not> page_directory_at p s \<and> \<not> asid_pool_at p s"
  apply (clarsimp simp: data_at_def obj_at_def a_type_def)
  apply (case_tac "kheap s p",simp)
  subgoal for ko
   by (case_tac ko,auto simp add: is_ep_def is_ntfn_def is_cap_table_def is_tcb_def)
  done

lemma data_at_pg_cap:
  "\<lbrakk>data_at sz p s;valid_cap cap s; p \<in> obj_refs cap\<rbrakk> \<Longrightarrow> is_pg_cap cap"
  apply (case_tac cap)
   apply (clarsimp simp: is_pg_cap_def obj_refs.simps valid_cap_def
                         data_at_orth split option.split)+
  apply (clarsimp split: arch_cap.split_asm simp: data_at_orth)
  done

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pg_inv\<rbrace> perform_page_invocation pg_inv \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases pg_inv, simp_all)
     \<comment> \<open>PageMap\<close>
     apply (rename_tac asid cap cslot_ptr sum)
     apply clarsimp
     apply (rule hoare_pre)
      apply (wp get_master_pte_wp get_master_pde_wp mapM_swp_store_pde_invs_unmap store_pde_invs_unmap' hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_arch_obj arch_update_cap_invs_map
             | wpc
             | simp add: pte_check_if_mapped_def pde_check_if_mapped_def del: fun_upd_apply
             | subst cte_wp_at_caps_of_state)+
       apply (wp_once hoare_drop_imp)
       apply (wp arch_update_cap_invs_map)
       apply (rule hoare_vcg_conj_lift)
        apply (rule hoare_lift_Pf[where f=vs_lookup, OF _ set_cap.vs_lookup])
        apply (rule_tac f="valid_pte xa" in hoare_lift_Pf[OF _ set_cap_valid_pte_stronger])
        apply wp
       apply (rule hoare_lift_Pf2[where f=vs_lookup, OF _ set_cap.vs_lookup])
       apply ((wp dmo_ccr_invs arch_update_cap_invs_map
                 hoare_vcg_const_Ball_lift
                 hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_typ_at
                 hoare_vcg_ex_lift hoare_vcg_ball_lift set_cap_arch_obj
                 set_cap.vs_lookup
              | wpc | simp add: same_refs_def del: fun_upd_apply split del: if_split
              | subst cte_wp_at_caps_of_state)+)
      apply (wp_once hoare_drop_imp)
      apply (wp arch_update_cap_invs_map hoare_vcg_ex_lift set_cap_arch_obj)
     apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state neq_Nil_conv
                           valid_slots_def empty_refs_def parent_for_refs_def
                 simp del: fun_upd_apply del: exE
                    split: sum.splits)
      apply (rule conjI)
       apply (clarsimp simp: is_cap_simps is_arch_update_def
                             cap_master_cap_simps
                      dest!: cap_master_cap_eqDs)
      apply clarsimp
      apply (rule conjI)
       apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
       apply (rule conjI)
        apply (clarsimp simp: is_arch_update_def is_pt_cap_def is_pg_cap_def
                              cap_master_cap_def image_def
                        split: Structures_A.cap.splits arch_cap.splits)
       apply (clarsimp simp: is_pt_cap_def cap_asid_def image_def neq_Nil_conv Collect_disj_eq
                      split: Structures_A.cap.splits arch_cap.splits option.splits)
      apply (rule conjI)
       apply (drule same_refs_lD)
       apply clarsimp
       apply fastforce
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (erule exEI)
      apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
      apply (clarsimp simp: same_refs_def)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
      apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
        apply assumption+
      apply (clarsimp simp: cap_range_def)
     apply (clarsimp)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
      apply (clarsimp split: Structures_A.kernel_object.split_asm
                            if_split_asm arch_kernel_obj.splits)
     apply (erule ballEI)
     apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
     apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
       apply assumption+
     apply (drule_tac x=sl in imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
     apply (drule (1) subsetD)
     apply (clarsimp simp: cap_range_def)
   \<comment> \<open>PageRemap\<close>
    apply (rule hoare_pre)
     apply (wp get_master_pte_wp get_master_pde_wp hoare_vcg_ex_lift mapM_x_swp_store_pde_invs_unmap
              | wpc | simp add: pte_check_if_mapped_def pde_check_if_mapped_def
              | (rule hoare_vcg_conj_lift, rule_tac slots=x2a in store_pde_invs_unmap'))+
    apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state
                          valid_slots_def empty_refs_def neq_Nil_conv
                    split: sum.splits)
     apply (clarsimp simp: parent_for_refs_def same_refs_def is_cap_simps cap_asid_def split: option.splits)
     apply (rule conjI, fastforce)
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
      apply clarsimp
      apply (erule (2) ref_is_unique[OF _ _ reachable_page_table_not_global])
              apply ((simp add: invs_def valid_state_def valid_arch_state_def
                                   valid_arch_caps_def valid_pspace_def valid_objs_caps)+)[9]
      apply fastforce
     apply( frule valid_global_refsD2)
      apply (clarsimp simp: cap_range_def parent_for_refs_def)+
    apply (rule conjI, rule impI)
     apply (rule exI, rule exI, rule exI)
     apply (erule conjI)
     apply clarsimp
    apply (rule conjI, rule impI)
     apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
     apply (clarsimp simp: same_refs_def pde_ref_def pde_ref_pages_def
                valid_pde_def invs_def valid_state_def valid_pspace_def)
     apply (drule valid_objs_caps)
     apply (clarsimp simp: valid_caps_def)
     apply (drule spec, drule spec, drule_tac x=capa in spec, drule (1) mp)
     apply (case_tac aa, (clarsimp simp add: data_at_pg_cap)+)[1]
    apply (clarsimp simp: pde_at_def obj_at_def a_type_def)

    apply (rule conjI)
     apply clarsimp
     apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
       apply simp+
     apply force
    apply (erule ballEI)
    apply clarsimp
    apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
      apply simp+
    apply force

   \<comment> \<open>PageUnmap\<close>
   apply (rename_tac arch_cap cslot_ptr)
   apply (rule hoare_pre)
    apply (wp dmo_invs arch_update_cap_invs_unmap_page get_cap_wp
              hoare_vcg_const_imp_lift | wpc | simp)+
      apply (rule_tac Q="\<lambda>_ s. invs s \<and>
                               cte_wp_at (\<lambda>c. is_pg_cap c \<and>
                                 (\<forall>ref. vs_cap_ref c = Some ref \<longrightarrow>
                                        \<not> (ref \<unrhd> obj_ref_of c) s)) cslot_ptr s"
                   in hoare_strengthen_post)
       prefer 2
       apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                             update_map_data_def
                             is_arch_update_def cap_master_cap_simps)
       apply (drule caps_of_state_valid, fastforce)
       apply (clarsimp simp: valid_cap_def cap_aligned_def vs_cap_ref_def
                      split: option.splits vmpage_size.splits cap.splits)
      apply (simp add: cte_wp_at_caps_of_state)
      apply (wp unmap_page_invs hoare_vcg_ex_lift hoare_vcg_all_lift
                hoare_vcg_imp_lift unmap_page_unmapped)+
   apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_arch_diminished_def)
   apply (drule (2) diminished_is_update')
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps is_arch_update_def
                         update_map_data_def cap_rights_update_def
                         acap_rights_update_def)
   using valid_validate_vm_rights[simplified valid_vm_rights_def]
   apply (auto simp: valid_cap_def cap_aligned_def mask_def vs_cap_ref_def data_at_def
                   split: vmpage_size.splits option.splits if_splits)[1]

  \<comment> \<open>PageFlush\<close>
  apply (rule hoare_pre)
   apply (wp dmo_invs set_vm_root_for_flush_invs
             hoare_vcg_const_imp_lift hoare_vcg_all_lift
          | simp)+
    apply (rule hoare_pre_imp[of _ \<top>], assumption)
    apply (clarsimp simp: valid_def)
    apply (thin_tac "p \<in> fst (set_vm_root_for_flush a b s)" for p a b)
    apply(safe)
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
            in use_valid)
       apply ((clarsimp | wp)+)[3]
    apply(erule use_valid, wp no_irq_do_flush no_irq, assumption)
   apply(wp set_vm_root_for_flush_invs | simp add: valid_page_inv_def tcb_at_invs)+
  done

end

locale asid_pool_map = Arch +
  fixes s ap pool asid pdp pd s'
  defines "(s' :: ('a::state_ext) state) \<equiv>
           s\<lparr>kheap := kheap s(ap \<mapsto> ArchObj (ASIDPool
                                               (pool(asid \<mapsto> pdp))))\<rparr>"
  assumes ap:  "kheap s ap = Some (ArchObj (ASIDPool pool))"
  assumes new: "pool asid = None"
  assumes pd:  "kheap s pdp = Some (ArchObj (PageDirectory pd))"
  assumes pde: "empty_table (set (second_level_tables (arch_state s)))
                            (ArchObj (PageDirectory pd))"
begin

definition
  "new_lookups \<equiv>
   {((rs,p),(rs',p')). rs' = VSRef (ucast asid) (Some AASIDPool) # rs \<and>
                       p = ap \<and> p' = pdp}"

lemma vs_lookup1:
  "vs_lookup1 s' = vs_lookup1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: if_split_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_trans:
  "(vs_lookup1 s')^* = (vs_lookup1 s)^* \<union> (vs_lookup1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def graph_of_def
                        empty_table_def pde_ref_def
                 split: if_split_asm)
  done

lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma new_lookups_rtrancl:
  "new_lookups^* = Id \<union> new_lookups"
  using ap pd
  apply -
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (erule rtrancl_induct2)
    apply clarsimp
   apply (clarsimp del: disjCI)
   apply (erule disjE)
    apply clarsimp
   apply (thin_tac "x \<in> R^*" for x R)
   apply (subgoal_tac "False", simp+)
   apply (clarsimp simp: new_lookups_def)
  apply (erule disjE, simp+)
  done

lemma vs_lookup:
  "vs_lookup s' = vs_lookup s \<union> new_lookups^* `` vs_lookup s"
  unfolding vs_lookup_def
  by (simp add: vs_lookup_trans relcomp_Image Un_Image)

lemma vs_lookup2:
  "vs_lookup s' = vs_lookup s \<union> (new_lookups `` vs_lookup s)"
  by (auto simp add: vs_lookup new_lookups_rtrancl)

lemma vs_lookup_pages1:
  "vs_lookup_pages1 s' = vs_lookup_pages1 s \<union> new_lookups"
  using pde pd new ap
  apply (clarsimp simp: vs_lookup_pages1_def new_lookups_def)
  apply (rule set_eqI)
  apply (clarsimp simp: obj_at_def s'_def vs_refs_pages_def graph_of_def)
  apply (rule iffI)
   apply (clarsimp simp: image_def split: if_split_asm)
   apply fastforce
  apply fastforce
  done

lemma vs_lookup_pages_trans:
  "(vs_lookup_pages1 s')^* =
   (vs_lookup_pages1 s)^* \<union> (vs_lookup_pages1 s)^* O new_lookups^*"
  using pd pde
  apply (simp add: vs_lookup_pages1)
  apply (rule union_trans)
  apply (subst (asm) new_lookups_def)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                        graph_of_def empty_table_def pde_ref_pages_def
                 split: if_split_asm)
  done

lemma vs_lookup_pages:
  "vs_lookup_pages s' =
   vs_lookup_pages s \<union> new_lookups^* `` vs_lookup_pages s"
  unfolding vs_lookup_pages_def
  by (simp add: vs_lookup_pages_trans relcomp_Image Un_Image)

lemma vs_lookup_pages2:
  "vs_lookup_pages s' = vs_lookup_pages s \<union> (new_lookups `` vs_lookup_pages s)"
  by (auto simp add: vs_lookup_pages new_lookups_rtrancl)

end

context Arch begin global_naming RISCV64

lemma not_kernel_slot_not_global_pt:
  "\<lbrakk>pde_ref (pd x) = Some p; x \<notin> kernel_mapping_slots;
    kheap s p' = Some (ArchObj (PageDirectory pd)); valid_kernel_mappings s\<rbrakk>
   \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pd_def)
   apply (drule_tac x="ArchObj (PageDirectory pd)" in bspec)
    apply ((fastforce simp: ran_def)+)[1]
   apply (simp add: second_level_tables_def split: arch_kernel_obj.split_asm)
  done

lemma set_asid_pool_arch_objs_map:
  "\<lbrace>valid_vspace_objs and valid_arch_state and valid_global_objs and
    valid_kernel_mappings and
    ko_at (ArchObj (ASIDPool pool)) ap and
    K (pool asid = None) and
    \<exists>\<rhd> ap and page_directory_at pd and
    (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s) \<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (2) valid_vspace_objsD)
  apply (clarsimp simp: valid_vspace_objs_def simp del: valid_vspace_obj.simps)
  apply (case_tac "p = ap")
   apply (clarsimp simp: obj_at_def
               simp del: fun_upd_apply valid_vspace_obj.simps)
   apply (clarsimp simp: ran_def)
   apply (case_tac "a = asid")
    apply clarsimp
    apply (rule typ_at_same_type)
      apply (simp add: obj_at_def a_type_simps)
     prefer 2
     apply assumption
    apply (simp add: a_type_def)
   apply clarsimp
   apply (erule allE, erule impE, rule exI, assumption)+
   apply (erule typ_at_same_type)
    prefer 2
    apply assumption
   apply (simp add: a_type_def)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (frule (3) asid_pool_map.intro)
  apply (subst (asm) asid_pool_map.vs_lookup, assumption)
  apply clarsimp
  apply (erule disjE)
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_rtrancl)
  apply (erule disjE)
   apply clarsimp
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_def empty_table_def)
  done

lemma obj_at_not_pt_not_in_global_pts:
  "\<lbrakk> obj_at P p s; valid_arch_state s; valid_global_objs s; \<And>pt. \<not> P (ArchObj (PageTable pt)) \<rbrakk>
          \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  unfolding second_level_tables_def
  apply (rule notI, drule(1) valid_global_ptsD)
  apply (clarsimp simp: obj_at_def)
  done

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_global_objs and valid_objs
    and valid_vspace_objs and ko_at (ArchObj (ASIDPool pool)) ap
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                   \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd
    and (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s)
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (frule obj_at_not_pt_not_in_global_pts[where p=pd], clarsimp+)
  apply (simp add: a_type_def)
  apply (frule obj_at_not_pt_not_in_global_pts[where p=ap], clarsimp+)
  apply (clarsimp simp: obj_at_def valid_arch_caps_def
                        caps_of_state_after_update)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm)
  apply (frule(3) asid_pool_map.intro)
  apply (simp add: fun_upd_def[symmetric])
  apply (rule conjI)
   apply (simp add: valid_vs_lookup_def
                    caps_of_state_after_update[folded fun_upd_def]
                    obj_at_def)
   apply (subst asid_pool_map.vs_lookup_pages2, assumption)
   apply simp
   apply (clarsimp simp: asid_pool_map.new_lookups_def)
   apply (frule(2) vs_lookup_vs_lookup_pagesI, simp add: valid_arch_state_def)
   apply (simp add: second_level_tables_def)
   apply (drule(2) ref_is_unique)
        apply (simp add: valid_vs_lookup_def)
       apply clarsimp+
     apply (simp add: valid_arch_state_def)
    apply (rule valid_objs_caps, simp)
   apply fastforce
  apply (simp add: valid_table_caps_def
                   caps_of_state_after_update[folded fun_upd_def] obj_at_def
              del: imp_disjL)
  apply (clarsimp simp del: imp_disjL)
  apply (drule(1) caps_of_state_valid_cap)+
  apply (auto simp add: valid_cap_def is_pt_cap_def is_pd_cap_def obj_at_def
                        a_type_def)[1]
  done

lemma set_asid_pool_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool pool)) ap
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (clarsimp split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (case_tac "p'=ap")
   apply (clarsimp simp: obj_at_def)
   apply (rule vs_lookupI)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def)
    apply fastforce
   apply (rule r_into_rtrancl)
   apply (rule_tac r="VSRef (a && mask asid_low_bits) (Some AASIDPool)" in vs_lookup1I)
     apply (simp add: obj_at_def)
    apply (simp add: vs_refs_def graph_of_def)
    apply fastforce
   apply simp
  apply (rule vs_lookupI)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply fastforce
  apply (rule r_into_rtrancl)
  apply (rule vs_lookup1I)
    apply (simp add: obj_at_def)
   apply simp
  apply simp
  done

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool pool)) ap
    and (\<lambda>s. \<exists>rf. (rf \<rhd> ap) s \<and> (\<exists>ptr cap. caps_of_state s ptr = Some cap
                                  \<and> pd \<in> obj_refs cap \<and> vs_cap_ref cap = Some ((VSRef (ucast asid) (Some AASIDPool)) # rf))
                              \<and> (VSRef (ucast asid) (Some AASIDPool) # rf \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None]))
    and page_directory_at pd
    and (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s)
    and K (pool asid = None)\<rbrace>
  set_asid_pool ap (pool(asid \<mapsto> pd))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_pre, wp valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_arch_objs_map valid_irq_handlers_lift
                            set_asid_pool_valid_arch_caps_map set_asid_pool_asid_map)
  apply clarsimp
  apply auto
  done

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def split: asid_pool_invocation.splits)
  apply (wp arch_update_cap_invs_map set_asid_pool_invs_map
            get_cap_wp set_cap_typ_at
            empty_table_lift[unfolded pred_conj_def, OF _ set_cap_obj_at_other]
            set_cap_obj_at_other
               |wpc|simp|wp_once hoare_vcg_ex_lift)+
  apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (frule caps_of_state_cteD)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp simp: cap_asid_def split: option.splits)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
  apply (rule conjI)
   apply (erule vs_lookup_atE)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule conjI)
    apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (clarsimp simp: vs_cap_ref_def mask_asid_low_bits_ucast_ucast)
   apply (clarsimp simp: asid_low_bits_def[symmetric] ucast_ucast_mask
                         word_neq_0_conv[symmetric])
   apply (erule notE, rule asid_low_high_bits, simp_all)[1]
   apply (simp add: asid_high_bits_of_def)
  apply (rule conjI)
   apply (erule(1) valid_table_caps_pdD [OF _ invs_pd_caps])
  apply (rule conjI)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: obj_at_def cte_wp_at_cases a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done

lemma invs_aligned_pdD:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (arm_global_pd (arch_state s)) pd_bits"
  apply (clarsimp simp: valid_arch_state_def)
  apply (drule (1) pd_aligned)
  apply (simp add: pd_bits_def pageBits_def)
  done

end
end
