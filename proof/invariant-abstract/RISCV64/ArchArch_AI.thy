(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchArch_AI
imports "../Arch_AI"
begin

context Arch begin global_naming RISCV64

definition
  "valid_aci aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
     \<lambda>s. cte_wp_at (\<lambda>c. c = NullCap) slot s \<and> real_cte_at slot s \<and>
         ex_cte_cap_wp_to is_cnode_cap slot s \<and>
         slot \<noteq> parent \<and>
         cte_wp_at (\<lambda>cap. \<exists>idx. cap = UntypedCap False frame pageBits idx) parent s \<and>
         descendants_of parent (cdt s) = {} \<and>
         is_aligned base asid_low_bits \<and>
         riscv_asid_table (arch_state s) (asid_high_bits_of base) = None"

lemma safe_parent_strg:
  "cte_wp_at (\<lambda>cap. cap = UntypedCap False frame pageBits idx) p s \<and>
   descendants_of p (cdt s) = {} \<and>
   valid_objs s
  \<longrightarrow>
  cte_wp_at (safe_parent_for (cdt s) p
             (ArchObjectCap (ASIDPoolCap frame base)))
             p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state safe_parent_for_def is_physical_def arch_is_physical_def)
  apply (rule is_aligned_no_overflow)
  apply (drule (1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  done

lemma range_cover_full:
  "\<lbrakk>is_aligned ptr sz; sz<word_bits\<rbrakk> \<Longrightarrow> range_cover (ptr::machine_word) sz sz (Suc 0)"
   by (clarsimp simp:range_cover_def unat_eq_0 le_mask_iff[symmetric] word_and_le1 word_bits_def)


definition
  valid_arch_inv :: "arch_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_inv ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti pti
   | InvokePage pgi \<Rightarrow> valid_page_inv pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci aci
   | InvokeASIDPool api \<Rightarrow> valid_apinv api"

lemma check_vp_wpR [wp]:
  "\<lbrace>\<lambda>s. vmsz_aligned w sz \<longrightarrow> P () s\<rbrace>
  check_vp_alignment sz w \<lbrace>P\<rbrace>, -"
  apply (simp add: check_vp_alignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp|wpc)+
  apply (simp add: vmsz_aligned_def)
  done


lemma check_vp_inv: "\<lbrace>P\<rbrace> check_vp_alignment sz w \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: check_vp_alignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp|wpc)+
  apply simp
  done


lemma p2_low_bits_max:
  "(2 ^ asid_low_bits - 1) = (max_word :: 9 word)"
  by (simp add: asid_low_bits_def max_word_def)


lemma dom_ucast_eq:
  "(- dom (\<lambda>a::asid_low_index. p (ucast a::machine_word)) \<inter> {x. ucast x + y \<noteq> 0} = {}) =
   (- dom p \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> x + y \<noteq> 0} = {})"
  apply safe
   apply clarsimp
   apply (rule ccontr)
   apply (erule_tac x="ucast x" in in_emptyE)
   apply (clarsimp simp: p2_low_bits_max)
   apply (rule conjI)
    apply (clarsimp simp: ucast_ucast_mask)
    apply (subst (asm) less_mask_eq)
    apply (rule word_less_sub_le [THEN iffD1])
      apply (simp add: word_bits_def)
     apply (simp add: asid_low_bits_def)
    apply simp
   apply (clarsimp simp: ucast_ucast_mask)
   apply (subst (asm) less_mask_eq)
   apply (rule word_less_sub_le [THEN iffD1])
     apply (simp add: word_bits_def)
    apply (simp add: asid_low_bits_def)
   apply simp
  apply (clarsimp simp: p2_low_bits_max)
  apply (rule ccontr)
  apply simp
  apply (erule_tac x="ucast x" in in_emptyE)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less, simp)
  apply (simp add: asid_low_bits_def)
  done


lemma asid_high_bits_max_word:
  "(2 ^ asid_high_bits - 1) = (max_word :: asid_high_index)"
  by (simp add: asid_high_bits_def max_word_def)


lemma dom_ucast_eq_8:
  "(- dom (\<lambda>a::asid_high_index. p (ucast a::machine_word)) = {}) =
   (- dom p \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} = {})"
  apply safe
   apply clarsimp
   apply (rule ccontr)
   apply (erule_tac x="ucast x" in in_emptyE)
   apply (clarsimp simp: asid_high_bits_max_word)
   apply (clarsimp simp: ucast_ucast_mask)
   apply (subst (asm) less_mask_eq)
   apply (rule word_less_sub_le [THEN iffD1])
     apply (simp add: word_bits_def)
    apply (simp add: asid_high_bits_def)
   apply simp
  apply (clarsimp simp: asid_high_bits_max_word)
  apply (rule ccontr)
  apply simp
  apply (erule_tac x="ucast x" in in_emptyE)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less, simp)
  apply (simp add: asid_high_bits_def)
  done


lemma ucast_fst_hd_assocs:
  "- dom (\<lambda>x. pool (ucast (x::asid_low_index)::machine_word)) \<inter> {x. ucast x + (w::machine_word) \<noteq> 0} \<noteq> {}
  \<Longrightarrow>
  fst (hd [(x, y)\<leftarrow>assocs pool . x \<le> 2 ^ asid_low_bits - 1 \<and> x + w \<noteq> 0 \<and> y = None]) =
  ucast (fst (hd [(x, y)\<leftarrow>assocs (\<lambda>a::asid_low_index. pool (ucast a)) .
                          x \<le> 2 ^ asid_low_bits - 1 \<and>
                          ucast x + w \<noteq> 0 \<and> y = None]))"
  apply (simp add: ucast_assocs[unfolded o_def])
  apply (simp add: filter_map split_def)
  apply (simp cong: conj_cong add: ucast_ucast_len)
  apply (simp add: asid_low_bits_def minus_one_norm)
  apply (simp add: ord_le_eq_trans [OF word_n1_ge])
  apply (simp add: word_le_make_less)
  apply (subgoal_tac "P" for P)  (* cut_tac but more awesome *)
   apply (subst hd_map, assumption)
   apply simp
   apply (rule sym, rule ucast_ucast_len)
   apply (drule hd_in_set)
   apply simp
  apply (simp add: assocs_empty_dom_comp null_def split_def)
  apply (simp add: ucast_assocs[unfolded o_def] filter_map split_def)
  apply (simp cong: conj_cong add: ucast_ucast_len)
  done


crunch typ_at [wp]:
  perform_page_table_invocation, perform_page_invocation, perform_asid_pool_invocation
  "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

lemmas perform_page_table_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_table_invocation_typ_at]

lemmas perform_page_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_page_invocation_typ_at]

lemmas perform_asid_pool_invocation_typ_ats [wp] =
  abs_typ_at_lifts [OF perform_asid_pool_invocation_typ_at]

lemma perform_asid_control_invocation_tcb_at:
  "\<lbrace>invs and valid_aci aci and st_tcb_at active p and
    K (\<forall>w a b c. aci = asid_control_invocation.MakePool w a b c \<longrightarrow> w \<noteq> p)\<rbrace>
  perform_asid_control_invocation aci
  \<lbrace>\<lambda>rv. tcb_at p\<rbrace>"
  apply (simp add: perform_asid_control_invocation_def)
  apply (cases aci)
  apply clarsimp
  apply (wp |simp)+
    apply (wp obj_at_delete_objects retype_region_obj_at_other2  hoare_vcg_const_imp_lift|assumption)+
  apply (intro impI conjI)
    apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def image_def ptr_add_def)
   apply (clarsimp simp: st_tcb_at_tcb_at)+
  apply (frule st_tcb_ex_cap)
    apply fastforce
   apply (clarsimp split: Structures_A.thread_state.splits)
   apply auto[1]
  apply (clarsimp simp: ex_nonz_cap_to_def valid_aci_def)
  apply (frule invs_untyped_children)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
      apply (simp add: cte_wp_at_caps_of_state)
     apply simp
    apply (simp add:cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: zobj_refs_to_obj_refs)
   apply (erule(1) in_empty_interE)
    apply (clarsimp simp:page_bits_def)
  apply simp
  done


lemma ucast_asid_high_btis_of_le [simp]:
  "ucast (asid_high_bits_of w) \<le> (2 ^ asid_high_bits - 1 :: machine_word)"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less)
   apply simp
  apply (simp add: asid_high_bits_def)
  done


lemma invoke_arch_tcb:
  "\<lbrace>invs and valid_arch_inv ai and st_tcb_at active tptr\<rbrace>
  arch_perform_invocation ai
  \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  apply (simp add: arch_perform_invocation_def)
  apply (cases ai; simp; (wp; clarsimp simp add: st_tcb_at_tcb_at)?)
  apply (wp perform_asid_control_invocation_tcb_at)
  apply (clarsimp simp add: valid_arch_inv_def)
  apply (clarsimp simp: valid_aci_def)
  apply (frule st_tcb_ex_cap)
    apply fastforce
   apply (clarsimp split: Structures_A.thread_state.splits)
   apply auto[1]
  apply (clarsimp simp: ex_nonz_cap_to_def)
  apply (frule invs_untyped_children)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
      apply (simp add: cte_wp_at_caps_of_state)+
    apply fastforce
   apply (clarsimp simp: zobj_refs_to_obj_refs cte_wp_at_caps_of_state)
   apply (drule_tac p="(aa,ba)" in caps_of_state_valid_cap, fastforce)
   apply (clarsimp simp: valid_cap_def cap_aligned_def)
   apply (drule_tac x=tptr in base_member_set, simp)
    apply (simp add: pageBits_def field_simps del: atLeastAtMost_iff)
   apply (metis (no_types) orthD1 x_power_minus_1)
  apply simp
  done

end


locale asid_update = Arch +
  fixes ap asid s s'
  assumes ko: "ko_at (ArchObj (ASIDPool Map.empty)) ap s"
  assumes empty: "asid_table s asid = None"
  defines "s' \<equiv> s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>"
(* FIXME RISCV: use asid_pools_of above *)

context asid_update begin

(* FIXME RISCV: translate *)
(*
lemma vs_lookup':
  "vs_lookup s' = vs_lookup s \<union> {([VSRef (ucast asid) None], ap)}"
  using ko
  apply (simp add: vs_lookup_def)
  apply (rule rtrancl_insert)
  apply (clarsimp simp: vs_lookup1_def obj_at_def vs_refs_def)
  done *)

(* FIXME RISCV: translate *)
(*
lemma vs_lookup_pages':
  "vs_lookup_pages s' = vs_lookup_pages s \<union> {([VSRef (ucast asid) None], ap)}"
  using ko
  apply (simp add: vs_lookup_pages_def)
  apply (rule rtrancl_insert)
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def)
  done *)

(* FIXME RISCV: translate *)
(*
lemma vs_lookup_neq: "\<lbrakk>(rs \<rhd> p) s' ; p \<noteq> ap\<rbrakk> \<Longrightarrow>  (rs \<rhd> p) s"
   by (clarsimp simp: vs_lookup')
*)


lemma obj_at [simp]:
  "obj_at P p s' = obj_at P p s"
  by (simp add: s'_def)

lemma vspace_objs':
  "valid_vspace_objs s \<Longrightarrow> valid_vspace_objs s'"
  using ko
  apply (clarsimp simp: valid_vspace_objs_def)
  sorry (* FIXME RISCV
  apply (erule_tac x=p in allE)
  apply (case_tac "p = ap";
         case_tac ao;
         fastforce simp: obj_at_def s'_def
                   intro: vs_lookup_neq)
  done *)

lemma global_objs':
  "valid_global_objs s \<Longrightarrow> valid_global_objs s'"
  by (simp add: valid_global_objs_def)

lemma caps_of_state_s':
  "caps_of_state s' = caps_of_state s"
  by (rule caps_of_state_pspace, simp add: s'_def)


lemma valid_vs_lookup':
  "\<lbrakk> valid_vs_lookup s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid, 0) \<rbrakk>
  \<Longrightarrow> valid_vs_lookup s'"
  sorry (* FIXME RISCV
  by (clarsimp simp: valid_vs_lookup_def caps_of_state_s' vs_lookup_pages') *)


lemma valid_table_caps':
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  by (simp add: valid_table_caps_def caps_of_state_s' s'_def)


lemma valid_asid_pool_caps':
  "\<lbrakk> valid_asid_pool_caps s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid, 0) \<rbrakk>
  \<Longrightarrow> valid_asid_pool_caps s'"
  sorry (* FIXME RISCV *)

lemma valid_arch_caps:
  "\<lbrakk> valid_arch_caps s;
     \<exists>ptr cap. caps_of_state s ptr = Some cap
     \<and> obj_refs cap = {ap} \<and> vs_cap_ref cap = Some (ucast asid, 0) \<rbrakk>
  \<Longrightarrow> valid_arch_caps s'"
  apply (simp add: valid_arch_caps_def valid_table_caps' valid_vs_lookup' valid_asid_pool_caps')
  apply (simp add: caps_of_state_s')
  done


lemma valid_asid_map':
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  by (clarsimp simp: valid_asid_map_def)

end


context Arch begin global_naming RISCV64

lemma valid_arch_state_strg:
  "valid_arch_state s \<and> ap \<notin> ran (riscv_asid_table (arch_state s)) \<and> asid_pool_at ap s \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def)
  apply (clarsimp simp: valid_asid_table_def ran_def)
  sorry (* FIXME RISCV
  apply (fastforce intro!: inj_on_fun_updI)
  done *)


lemma valid_vs_lookup_at_upd_strg:
  "valid_vs_lookup s \<and>
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   riscv_asid_table (arch_state s) asid = None \<and>
   (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {ap} \<and>
              vs_cap_ref cap = Some (ucast asid, 0))
   \<longrightarrow>
   valid_vs_lookup (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (subgoal_tac "asid_update ap asid s")
   prefer 2
   apply unfold_locales[1]
    apply assumption+
  apply (erule (1) asid_update.valid_vs_lookup')
  apply fastforce
  done


lemma retype_region_ap:
  "\<lbrace>\<top>\<rbrace>
  retype_region ap 1 0 (ArchObject ASIDPoolObj) dev
  \<lbrace>\<lambda>_. ko_at (ArchObj (ASIDPool Map.empty)) ap\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule retype_region_obj_at)
    apply simp
   apply simp
  apply (clarsimp simp: retype_addrs_def obj_bits_api_def default_arch_object_def)
  apply (clarsimp simp: obj_at_def default_object_def default_arch_object_def)
  done


lemma retype_region_ap':
  "\<lbrace>\<top>\<rbrace> retype_region ap 1 0 (ArchObject ASIDPoolObj) dev \<lbrace>\<lambda>rv. asid_pool_at ap\<rbrace>"
  apply (rule hoare_strengthen_post, rule retype_region_ap)
  apply (clarsimp simp: a_type_def elim!: obj_at_weakenE)
  done


lemma no_cap_to_obj_with_diff_ref_null_filter:
  "no_cap_to_obj_with_diff_ref cap S
     = (\<lambda>s. \<forall>c \<in> ran (null_filter (caps_of_state s) |` (- S)).
             obj_refs c = obj_refs cap
                 \<longrightarrow> table_cap_ref c = table_cap_ref cap)"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   ball_ran_eq cte_wp_at_caps_of_state)
  apply (simp add: Ball_def)
  apply (intro iff_allI ext)
  apply (simp add: restrict_map_def null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


lemma retype_region_no_cap_to_obj:
  "\<lbrace>valid_pspace and valid_mdb
             and caps_overlap_reserved {ptr..ptr + 2 ^ obj_bits_api ty us - 1}
             and caps_no_overlap ptr sz
             and pspace_no_overlap_range_cover ptr sz
             and no_cap_to_obj_with_diff_ref cap S
             and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
             and K (ty = CapTableObject \<longrightarrow> 0 < us)
             and K (range_cover ptr sz (obj_bits_api ty us) 1) \<rbrace>
     retype_region ptr 1 us ty dev
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: no_cap_to_obj_with_diff_ref_null_filter)
  apply (wp retype_region_caps_of | simp)+
  apply fastforce
  done


lemma valid_table_caps_asid_upd [iff]:
  "valid_table_caps (s\<lparr>arch_state := (riscv_asid_table_update f (arch_state s))\<rparr>) =
   valid_table_caps s"
  by (simp add: valid_table_caps_def second_level_tables_def)


(* FIXME RISCV: probably translate
lemma vs_asid_ref_upd:
  "([VSRef (ucast (asid_high_bits_of asid')) None] \<rhd> ap')
    (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)
  = (if asid_high_bits_of asid' = asid_high_bits_of asid
    then ap' = ap
    else ([VSRef (ucast (asid_high_bits_of asid')) None] \<rhd> ap') s)"
  by (fastforce intro: vs_lookup_atI elim: vs_lookup_atE)
*)


(* FIXME RISCV: probably translate
lemma vs_asid_ref_eq:
  "([VSRef (ucast asid) None] \<rhd> ap) s
  = (riscv_asid_table (arch_state s) asid = Some ap)"
  by (fastforce elim: vs_lookup_atE intro: vs_lookup_atI)
*)

lemma set_cap_reachable_pg_cap:
  "\<lbrace>\<lambda>s. P (reachable_frame_cap cap s)\<rbrace> set_cap x y \<lbrace>\<lambda>_ s. P (reachable_frame_cap cap s)\<rbrace>"
  unfolding reachable_frame_cap_def reachable_target_def vs_lookup_target_def
  apply (clarsimp simp: in_omonad vs_lookup_slot_def vs_lookup_table_def)
  apply (wp_pre, wps, wp)
  apply simp
  done

lemma cap_insert_simple_arch_caps_ap:
  "\<lbrace>valid_arch_caps and (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s)
     and no_cap_to_obj_with_diff_ref cap {dest}
     and (\<lambda>s. riscv_asid_table (arch_state s) (asid_high_bits_of asid) = None)
     and ko_at (ArchObj (ASIDPool Map.empty)) ap
     and K (cap = ArchObjectCap (ASIDPoolCap ap asid)) \<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv s. valid_arch_caps (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: cap_insert_def update_cdt_def set_cdt_def valid_arch_caps_def
                   set_untyped_cap_as_full_def bind_assoc)
  apply (strengthen valid_vs_lookup_at_upd_strg)
  apply (wp get_cap_wp set_cap_valid_vs_lookup set_cap_arch_obj
            set_cap_valid_table_caps hoare_vcg_all_lift
          | simp split del: if_split)+
  sorry (* FIXME RISCV
       apply (rule_tac P = "cte_wp_at ((=) src_cap) src" in set_cap_orth)
       apply (wp hoare_vcg_imp_lift hoare_vcg_ball_lift set_free_index_final_cap
                 hoare_vcg_disj_lift set_cap_reachable_pg_cap set_cap.vs_lookup_pages
              | clarsimp)+
      apply_trace (wp set_cap_arch_obj set_cap_valid_table_caps hoare_vcg_ball_lift
                get_cap_wp static_imp_wp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (rule_tac x="fst dest" in exI)
   apply (rule_tac x="snd dest" in exI)
   apply simp
  apply (rule conjI)
   apply (simp add: unique_table_caps_def is_cap_simps)
  apply (subst unique_table_refs_def)
  apply (intro allI impI)
  apply (simp split: if_split_asm)
    apply (simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
   apply (simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
  apply (erule (3) unique_table_refsD)
  done *)

lemma valid_asid_map_asid_upd_strg:
  "valid_asid_map s \<and>
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   riscv_asid_table (arch_state s) asid = None \<longrightarrow>
   valid_asid_map (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  by (simp add: valid_asid_map_def)

lemma valid_vspace_objs_asid_upd_strg:
  "valid_vspace_objs s \<and>
   ko_at (ArchObj (ASIDPool Map.empty)) ap s \<and>
   riscv_asid_table (arch_state s) asid = None \<longrightarrow>
   valid_vspace_objs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  apply clarsimp
  apply (subgoal_tac "asid_update ap asid s")
   prefer 2
   apply unfold_locales[1]
    apply assumption+
  apply (erule (1) asid_update.vspace_objs')
  done

lemma valid_global_objs_asid_upd_strg:
  "valid_global_objs s \<and>
   ko_at (ArchObj (arch_kernel_obj.ASIDPool Map.empty)) ap s \<and>
   riscv_asid_table (arch_state s) asid = None \<longrightarrow>
   valid_global_objs (s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := riscv_asid_table (arch_state s)(asid \<mapsto> ap)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_global_objs_def)

lemma safe_parent_cap_is_device:
  "safe_parent_for m p cap pcap \<Longrightarrow> cap_is_device cap = cap_is_device pcap"
  by (simp add: safe_parent_for_def)

lemma cap_insert_ioports_ap:
  "\<lbrace>valid_ioports and (\<lambda>s. cte_wp_at (\<lambda>cap'. safe_ioport_insert cap cap' s) dest s) and
        K (is_ap_cap cap)\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  by wpsimp

lemma cap_insert_ap_invs:
  "\<lbrace>invs and valid_cap cap and tcb_cap_valid cap dest and
    ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
    cte_wp_at (\<lambda>c. c = NullCap) dest and
    no_cap_to_obj_with_diff_ref cap {dest} and
    (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
    K (cap = ArchObjectCap (ASIDPoolCap ap asid)) and
   (\<lambda>s. \<forall>irq \<in> cap_irqs cap. irq_issued irq s) and
   ko_at (ArchObj (ASIDPool Map.empty)) ap and
   (\<lambda>s. ap \<notin> ran (riscv_asid_table (arch_state s)) \<and>
        riscv_asid_table (arch_state s) (asid_high_bits_of asid) = None)\<rbrace>
  cap_insert cap src dest
  \<lbrace>\<lambda>rv s. invs (s\<lparr>arch_state := arch_state s
                       \<lparr>riscv_asid_table := (riscv_asid_table \<circ> arch_state) s(asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (strengthen valid_arch_state_strg valid_vspace_objs_asid_upd_strg
                    valid_asid_map_asid_upd_strg )
  apply (simp cong: conj_cong)
  apply (rule hoare_pre)
   apply (wp cap_insert_simple_mdb cap_insert_iflive
             cap_insert_zombies cap_insert_ifunsafe cap_insert_ioports_ap
             cap_insert_valid_global_refs cap_insert_idle
             valid_irq_node_typ cap_insert_simple_arch_caps_ap)
  sorry (* FIXME RISCV
  apply (clarsimp simp: is_simple_cap_def cte_wp_at_caps_of_state is_cap_simps)
  apply (frule safe_parent_cap_is_device)
  apply (drule safe_parent_cap_range)
  apply simp
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule_tac p="(a,b)" in caps_of_state_valid_cap, fastforce)
  apply (auto simp: obj_at_def is_tcb_def is_cap_table_def
                    valid_cap_def [where c="cap.Zombie a b x" for a b x]
              dest: obj_ref_is_tcb obj_ref_is_cap_table split: option.splits)
  done *)


lemma max_index_upd_no_cap_to:
  "\<lbrace>\<lambda>s. no_cap_to_obj_with_diff_ref cap {slot} s \<and>
        cte_wp_at ((=) ucap) cref s \<and> is_untyped_cap ucap\<rbrace>
   set_cap (max_free_index_update ucap) cref
   \<lbrace>\<lambda>rv s. no_cap_to_obj_with_diff_ref cap {slot} s \<rbrace>"
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def)
  apply (wp hoare_vcg_ball_lift set_cap_cte_wp_at_neg)
  apply (clarsimp simp:cte_wp_at_caps_of_state free_index_update_def is_cap_simps)
  apply (drule_tac x = cref in bspec)
   apply clarsimp
  apply (clarsimp simp:table_cap_ref_def)
  done

lemma perform_asid_control_invocation_st_tcb_at:
  "\<lbrace>st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t
    and ct_active and invs and valid_aci aci\<rbrace>
    perform_asid_control_invocation aci
  \<lbrace>\<lambda>y. st_tcb_at P t\<rbrace>"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (clarsimp simp: perform_asid_control_invocation_def split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (rule hoare_name_pre_state)
  apply (subgoal_tac "is_aligned word1 page_bits")
   prefer 2
   apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
   apply (drule(1) caps_of_state_valid[rotated])+
   apply (simp add:valid_cap_simps cap_aligned_def page_bits_def)
  apply (subst delete_objects_rewrite)
     apply (simp add:page_bits_def word_bits_def pageBits_def word_size_bits_def)+
   apply (simp add:is_aligned_neg_mask_eq)
  apply (wp hoare_vcg_const_imp_lift retype_region_st_tcb_at[where sz=page_bits] set_cap_no_overlap|simp)+
     apply (strengthen invs_valid_objs invs_psp_aligned)
     apply (clarsimp simp:conj_comms)
     apply (wp max_index_upd_invs_simple get_cap_wp)+
  apply (clarsimp simp: valid_aci_def)
  apply (frule intvl_range_conv)
   apply (simp add:word_bits_def page_bits_def pageBits_def)
  apply (clarsimp simp:detype_clear_um_independent page_bits_def is_aligned_neg_mask_eq)
  apply (rule conjI)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (simp only: field_simps)
   apply (rule pspace_no_overlap_detype')
     apply (rule caps_of_state_valid_cap)
      apply (simp add:page_bits_def)+
    apply (simp add:invs_valid_objs invs_psp_aligned)+
  apply (rule conjI)
   apply (erule pred_tcb_weakenE, simp)
  apply (rule conjI)
   apply (frule st_tcb_ex_cap)
     apply clarsimp
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (frule invs_untyped_children)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (erule_tac ptr="(aa,ba)" in untyped_children_in_mdbE[where P="\<lambda>c. t \<in> zobj_refs c" for t])
       apply (simp add: cte_wp_at_caps_of_state)+
      apply fastforce
    apply (clarsimp simp: zobj_refs_to_obj_refs)
    apply (fastforce simp:page_bits_def)
   apply simp
  apply (clarsimp simp:obj_bits_api_def arch_kobj_size_def cte_wp_at_caps_of_state
    default_arch_object_def empty_descendants_range_in)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state
      empty_descendants_range_in descendants_range_def2)+
  apply (thin_tac "x = Some cap.NullCap" for x)+
  apply (drule(1) caps_of_state_valid_cap[OF _ invs_valid_objs])
  apply (intro conjI)
    apply (clarsimp simp:valid_cap_def cap_aligned_def range_cover_full
     invs_psp_aligned invs_valid_objs page_bits_def)
   apply (erule pspace_no_overlap_detype)
  apply (auto simp:page_bits_def detype_clear_um_independent)
  done

lemma set_cap_idx_up_aligned_area:
  "\<lbrace>K (\<exists>idx. pcap = UntypedCap dev ptr pageBits idx) and cte_wp_at ((=) pcap) slot
      and valid_objs\<rbrace> set_cap (max_free_index_update pcap) slot
  \<lbrace>\<lambda>rv s. (\<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr pageBits \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)\<rbrace>"
  apply (rule hoare_pre)
  apply (wp hoare_vcg_ex_lift set_cap_cte_wp_at)
  apply (rule_tac x = slot in exI)
  apply clarsimp
  apply (frule(1) cte_wp_valid_cap)
  apply (clarsimp simp: cte_wp_at_caps_of_state p_assoc_help valid_cap_def valid_untyped_def
                        cap_aligned_def)
  done

primrec(nonexhaustive)
  get_untyped_cap_idx :: "cap \<Rightarrow> nat"
where
  "get_untyped_cap_idx (UntypedCap dev ref sz idx) = idx"

lemma aci_invs':
  assumes Q_ignores_arch[simp]: "\<And>f s. Q (arch_state_update f s) = Q s"
  assumes Q_ignore_machine_state[simp]: "\<And>f s. Q (machine_state_update f s) = Q s"
  assumes Q_detype[simp]: "\<And>f s. Q (detype f s) = Q s"
  assumes cap_insert_Q: "\<And>cap src dest. \<lbrace>Q and invs and K (src \<noteq> dest)\<rbrace>
                            cap_insert cap src dest
                           \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes retype_region_Q[wp]:"\<And>a b c d e. \<lbrace>Q\<rbrace> retype_region a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_cap_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_cap a b \<lbrace>\<lambda>_.Q\<rbrace>"
  shows
  "\<lbrace>invs and Q and ct_active and valid_aci aci\<rbrace> perform_asid_control_invocation aci \<lbrace>\<lambda>y s. invs s \<and> Q s\<rbrace>"
  proof -
  have cap_insert_invsQ:
       "\<And>cap src dest ap asid.
        \<lbrace>Q and (invs and valid_cap cap and tcb_cap_valid cap dest and
         ex_cte_cap_wp_to (appropriate_cte_cap cap) dest and
         cte_wp_at (\<lambda>c. c = NullCap) dest and
         no_cap_to_obj_with_diff_ref cap {dest} and
         (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src cap) src s) and
         K (cap = ArchObjectCap (ASIDPoolCap ap asid)) and
         (\<lambda>s. \<forall>irq\<in>cap_irqs cap. irq_issued irq s) and
         ko_at (ArchObj (ASIDPool Map.empty)) ap and
         (\<lambda>s. ap \<notin> ran (riscv_asid_table (arch_state s)) \<and>
         riscv_asid_table (arch_state s) (asid_high_bits_of asid) = None))\<rbrace>
         cap_insert cap src dest
        \<lbrace>\<lambda>rv s.
           invs
             (s\<lparr>arch_state := arch_state s
                 \<lparr>riscv_asid_table := (riscv_asid_table \<circ> arch_state) s
                    (asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>) \<and>
           Q
             (s\<lparr>arch_state := arch_state s
                 \<lparr>riscv_asid_table := (riscv_asid_table \<circ> arch_state) s
                    (asid_high_bits_of asid \<mapsto> ap)\<rparr>\<rparr>)\<rbrace>"
        apply (wp cap_insert_ap_invs)
        apply simp
        apply (rule hoare_pre)
        apply (rule cap_insert_Q)
        apply (auto simp: cte_wp_at_caps_of_state)
        done
  show ?thesis
  apply (clarsimp simp: perform_asid_control_invocation_def valid_aci_def
    split: asid_control_invocation.splits)
  apply (rename_tac word1 a b aa ba word2)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift)
     apply (wp cap_insert_invsQ hoare_vcg_ex_lift
             | simp)+
    apply (simp add: valid_cap_def |
           strengthen real_cte_tcb_valid safe_parent_strg
                      invs_vobjs_strgs
                      ex_cte_cap_to_cnode_always_appropriate_strg)+
    apply (wp hoare_vcg_const_imp_lift set_free_index_invs
              retype_region_plain_invs[where sz = pageBits]
              retype_cte_wp_at[where sz = pageBits] hoare_vcg_ex_lift
              retype_region_obj_at_other3[where P="is_cap_table n" and sz = pageBits for n]
              retype_region_ex_cte_cap_to[where sz = pageBits]
              retype_region_ap[simplified]
              retype_region_ap'[simplified]
              retype_region_no_cap_to_obj[where sz = pageBits,simplified]
               | simp del: split_paired_Ex)+
    apply (strengthen invs_valid_objs invs_psp_aligned
           invs_mdb invs_valid_pspace
           exI[where x="case aci of MakePool frame slot parent base \<Rightarrow> parent"]
           exI[where x="case aci of MakePool frame slot parent base \<Rightarrow> parent",
             simplified]
           caps_region_kernel_window_imp[where
             p = "case aci of MakePool frame slot parent base \<Rightarrow> parent"]
           invs_cap_refs_in_kernel_window)+
    apply (wp set_cap_caps_no_overlap set_cap_no_overlap get_cap_wp
      max_index_upd_caps_overlap_reserved max_index_upd_invs_simple
      set_cap_cte_cap_wp_to set_cap_cte_wp_at max_index_upd_no_cap_to
      | simp split del: if_split | wp_once hoare_vcg_ex_lift)+
    apply (rule_tac P = "is_aligned word1 page_bits" in hoare_gen_asm)
    apply (subst delete_objects_rewrite)
       apply (simp add:page_bits_def pageBits_def word_size_bits_def)
      apply (simp add:page_bits_def pageBits_def word_bits_def)
     apply (simp add: page_bits_def)
    apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state if_option_Some
                        Word_Miscellaneous.if_bool_simps
             split del: if_split)
  apply (strengthen refl)
  apply (frule_tac cap = "(cap.UntypedCap False word1 pageBits idx)"
    in detype_invariants[rotated 3],clarsimp+)
    apply (simp add:cte_wp_at_caps_of_state)+
   apply (simp add:descendants_range_def2 empty_descendants_range_in)
  apply (simp add:invs_mdb invs_valid_pspace invs_psp_aligned invs_valid_objs)
  apply (clarsimp dest!:caps_of_state_cteD)
  apply (frule(1) unsafe_protected[where p=t and p'=t for t])
     apply (simp add:empty_descendants_range_in)+
    apply fastforce
   apply clarsimp
  apply (frule_tac p = "(aa,ba)" in cte_wp_valid_cap)
   apply fastforce
  apply (clarsimp simp: detype_clear_um_independent obj_bits_api_def arch_kobj_size_def
   default_arch_object_def conj_comms)
  apply (rule conjI)
   apply (clarsimp simp:valid_cap_simps cap_aligned_def page_bits_def not_le)
  apply clarsimp
  apply (simp add:empty_descendants_range_in)
  apply (frule valid_cap_aligned)
  apply (clarsimp simp: cap_aligned_def is_aligned_neg_mask_eq)
  apply (subst caps_no_overlap_detype[OF descendants_range_caps_no_overlapI],
    assumption, simp add: is_aligned_neg_mask_eq,
    simp add: empty_descendants_range_in)
  apply (frule pspace_no_overlap_detype, clarify+)
  apply (frule intvl_range_conv[where bits = pageBits])
   apply (simp add:pageBits_def word_bits_def)
  sorry (* FIXME RISCV
  apply (simp add:is_aligned_neg_mask_eq)
  apply (clarsimp simp:is_aligned_neg_mask_eq page_bits_def)
  apply (frule(1) ex_cte_cap_protects)
      apply (simp add:empty_descendants_range_in)
     apply fastforce
    apply (rule subset_refl)
   apply fastforce
  apply (clarsimp simp: field_simps)
  apply (intro conjI impI,
     simp_all add:free_index_of_def valid_cap_simps valid_untyped_def
     empty_descendants_range_in range_cover_full clear_um_def max_free_index_def,
     (clarsimp simp:valid_untyped_def valid_cap_simps)+)[1]

    apply (erule(1) cap_to_protected)
    apply (simp add:empty_descendants_range_in descendants_range_def2)+

   apply clarsimp
   apply (drule invs_arch_state)+
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
   apply (drule (1) bspec)+
   apply clarsimp
   apply (erule notE, erule is_aligned_no_overflow)

  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def)
  apply (thin_tac "cte_wp_at ((=) cap.NullCap) p s" for p s)
  apply (subst(asm) eq_commute,
         erule(1) untyped_children_in_mdbE[where cap="cap.UntypedCap dev p bits idx" for dev p bits idx,
                                         simplified, rotated])
    apply (simp add: is_aligned_no_overflow)
   apply simp
  apply clarsimp
  done *)

qed


lemmas aci_invs[wp] =
  aci_invs'[where Q=\<top>,simplified hoare_post_taut, OF refl refl refl TrueI TrueI TrueI,simplified]

lemma invoke_arch_invs[wp]:
  "\<lbrace>invs and ct_active and valid_arch_inv ai\<rbrace>
   arch_perform_invocation ai
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv_def arch_perform_invocation_def)
  apply (wp|simp)+
  done

lemma sts_vspace_at_asid [wp]:
  "set_thread_state t st \<lbrace>vspace_at_asid asid pd\<rbrace>"
  apply (simp add: vspace_at_asid_def)
  sorry (* FIXME RISCV
  apply wpsimp
  done *)

lemma sts_valid_slots_inv[wp]:
  "\<lbrace>valid_slots m\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  sorry (* FIXME RISCV
  by (cases m; case_tac a; clarsimp simp: valid_slots_def; wp hoare_vcg_ball_lift sts_typ_ats)
  *)


lemma sts_valid_page_inv[wp]:
"\<lbrace>valid_page_inv page_invocation\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_page_inv page_invocation\<rbrace>"
  sorry (* FIXME RISCV
  by (cases page_invocation,
       (wp hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_imp_lift sts_typ_ats
        | clarsimp simp: valid_page_inv_def
        | wps)+) *)


crunch global_refs_inv[wp]: set_thread_state "\<lambda>s. P (global_refs s)"

lemma sts_empty_table[wp]:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) p s\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (second_level_tables (arch_state s)))) p s\<rbrace>"
  sorry (* FIXME RISCV
  by (rule hoare_lift_Pf[OF sts.aobj_at[OF empty_table.arch_only] sts.arch_state]) *)

lemma sts_valid_vspace_table_inv[wp]:
  "\<And>i. \<lbrace>valid_pti i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_pti i\<rbrace>"
  sorry (* FIXME RISCV
  by (case_tac i; simp add: valid_pti_def;
      wp sts_typ_ats hoare_vcg_ex_lift; clarsimp) *)


lemma sts_valid_arch_inv:
  "\<lbrace>valid_arch_inv ai\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_arch_inv ai\<rbrace>"
  apply (cases ai; simp add: valid_arch_inv_def; wp?)
   apply (rename_tac asid_control_invocation)
   apply (case_tac asid_control_invocation)
   apply (clarsimp simp: valid_aci_def cte_wp_at_caps_of_state)
   apply (rule hoare_pre, wp hoare_vcg_ex_lift cap_table_at_typ_at)
   apply clarsimp
  apply (clarsimp simp: valid_apinv_def split: asid_pool_invocation.splits)
  sorry (* FIXME RISCV
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift set_thread_state_ko)
  apply (clarsimp simp: is_tcb_def)
  apply (rename_tac ioc, case_tac ioc)
  apply (clarsimp simp: valid_iocontrol_inv_def)
  apply (wpsimp simp: safe_ioport_insert_def)
  done *)


crunch_ignore (add: select_ext find_vspace_for_asid)


crunch inv [wp]: arch_decode_invocation "P"
  (wp: crunch_wps select_wp select_ext_weak_wp simp: crunch_simps)


declare lookup_slot_for_cnode_op_cap_to [wp]


lemma shiftr_irrelevant:
  "x < 2 ^ asid_low_bits \<Longrightarrow> is_aligned (y :: machine_word) asid_low_bits \<Longrightarrow>
    x + y >> asid_low_bits = y >> asid_low_bits"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: is_aligned_nth)
   apply (drule(1) nth_bounded)
    apply (simp add: asid_low_bits_def word_bits_def)
   apply simp
  apply (rule word_eqI)
  apply (simp add: nth_shiftr)
  apply safe
  apply (drule(1) nth_bounded)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply simp
  done

(* FIXME RISCV: probably translate
lemma lookup_pt_slot_cap_to:
  "\<lbrace>invs and \<exists>\<rhd>pm and K (is_aligned pm pml4_bits \<and> vptr < pptr_base \<and> canonical_address vptr)\<rbrace>
    lookup_pt_slot pm vptr
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> is_pt_cap cap
                                \<and> rv && ~~ mask pt_bits \<in> obj_refs cap
                                \<and> s \<turnstile> cap \<and> cap_asid cap \<noteq> None\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (wp lookup_pt_slot_wp)
  apply clarsimp
  apply (drule_tac x=ref in spec)
  apply (erule impE, fastforce, clarsimp)
  apply (thin_tac "(_ \<rhd> pm) _")
  apply (frule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]; clarsimp)
  apply (intro exI, rule conjI, assumption)
  apply (frule (1) caps_of_state_valid)
  apply (clarsimp simp: pte_at_def)
  apply (frule (2) valid_cap_to_pt_cap')
  by (auto simp: vs_cap_ref_def is_pt_cap_def
          split: cap.splits arch_cap.splits option.splits)
*)


(* FIXME RISCV: needed?
lemma find_vspace_for_asid_ref_offset_voodoo:
  "\<lbrace>pspace_aligned and valid_vspace_objs and
         K (ref = [VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                   VSRef (ucast (asid_high_bits_of asid)) None])\<rbrace>
      find_vspace_for_asid asid
   \<lbrace>\<lambda>rv. (ref \<rhd> (rv + (get_pml4_index v  << word_size_bits) && ~~ mask pml4_bits))\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (rule_tac Q'="\<lambda>rv s. is_aligned rv pml4_bits \<and> (ref \<rhd> rv) s"
               in hoare_post_imp_R)
   apply simp
   apply (rule hoare_pre, wp find_vspace_for_asid_lookup_ref)
   apply simp
  apply (simp add: pml4_shifting)
  done
*)


declare asid_high_bits_of_shift [simp]
declare mask_shift [simp]
declare word_less_sub_le [simp del]
declare ptrFormPAddr_addFromPPtr [simp]


(* FIXME: move *)
lemma valid_mask_vm_rights[simp]:
  "mask_vm_rights V R \<in> valid_vm_rights"
  by (simp add: mask_vm_rights_def)

(* FIXME RISCV: looks duplicate-ish
lemma vs_lookup_and_unique_refs:
  "\<lbrakk>(ref \<rhd> p) s; caps_of_state s cptr = Some cap; table_cap_ref cap = Some ref';
    p \<in> obj_refs cap; valid_vs_lookup s; unique_table_refs (caps_of_state s)\<rbrakk>
   \<Longrightarrow> ref = ref'"
  apply (frule_tac ref=ref in valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], assumption)
  apply clarsimp
  apply (frule_tac cap'=capa in unique_table_refsD)
     apply simp+
   apply (case_tac capa, simp_all)
        apply ((case_tac cap, simp_all)+)[6]
     apply (clarsimp simp add: table_cap_ref_def vs_cap_ref_def split: cap.splits arch_cap.splits option.splits)
  done
*)

lemma cte_wp_at_page_cap_weaken:
  "cte_wp_at (diminished (ArchObjectCap (FrameCap word seta vmpage_size dev None))) slot s \<Longrightarrow>
   cte_wp_at (\<lambda>a. \<exists>p R sz dev m. a = ArchObjectCap (FrameCap p R sz dev m)) slot s"
  apply (clarsimp simp: cte_wp_at_def diminished_def mask_cap_def cap_rights_update_def)
  apply (clarsimp simp: acap_rights_update_def split: cap.splits arch_cap.splits)
  done

(* FIXME RISCV: no longer the case for huge pages after kernel_base update
lemma aligned_sum_less_kernel_base:
  "vmsz_aligned p sz \<Longrightarrow> (p + 2 ^ pageBitsForSize sz - 1 < kernel_base) = (p < kernel_base)"
  apply (rule iffI)
   apply (rule le_less_trans)
    apply (rule is_aligned_no_overflow)
    apply (simp add: vmsz_aligned_def)
   apply simp
  apply (simp add:field_simps[symmetric])
  apply (erule gap_between_aligned)
    apply (simp add: vmsz_aligned_def)+
   apply (case_tac sz; simp add: kernel_base_def bit_simps is_aligned_def)
  done
*)

lemma le_user_vtop_less_pptr_base[simp]:
  "x \<le> user_vtop \<Longrightarrow> x < pptr_base"
  using dual_order.strict_trans2 by blast

lemmas le_user_vtop_canonical_address = below_user_vtop_canonical[simp]

lemma decode_page_invocation_wf[wp]:
  "arch_cap = FrameCap word rights vmpage_size dev option \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at (diminished (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (diminished (fst x)) (snd x) s)\<rbrace>
    decode_frame_invocation label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  sorry (* FIXME RISCV
  apply (simp add: arch_decode_invocation_def decode_frame_invocation_def Let_def split_def
                 cong: if_cong split del: if_split)
  apply (cases "invocation_type label = ArchInvocationLabel RISCVPageMap")
   apply (simp split del: if_split)
   apply (rule hoare_pre)
    apply ((wp whenE_throwError_wp check_vp_wpR hoare_vcg_const_imp_lift_R
                | wpc
                | simp add: valid_arch_inv_def valid_page_inv_def is_frame_cap_def)+)
   apply (clarsimp simp: neq_Nil_conv invs_vspace_objs)
   apply (frule diminished_cte_wp_at_valid_cap[where p="(a, b)" for a b], clarsimp)
   apply (frule diminished_cte_wp_at_valid_cap[where p=slot], clarsimp)
   apply (clarsimp simp: cte_wp_at_caps_of_state mask_cap_def
                             diminished_def[where cap="ArchObjectCap (PageCap d x y t z w)" for d x y t z w]
                             linorder_not_le aligned_sum_less_kernel_base
                  dest!: diminished_pm_capD)
   apply (clarsimp simp: cap_rights_update_def acap_rights_update_def
                  split: cap.splits arch_cap.splits)
   apply (auto,
              auto simp: cte_wp_at_caps_of_state invs_def valid_state_def
                         valid_cap_simps is_arch_update_def
                         is_arch_cap_def cap_master_cap_simps
                         vs_cap_ref_def cap_aligned_def bit_simps data_at_def
                         vmsz_aligned_def
                  split: vmpage_size.split if_splits,
              (fastforce intro: diminished_pm_self)+)[1]
  apply (cases "invocation_type label = ArchInvocationLabel RISCVPageRemap")
   apply (simp split del: if_split)
   apply (rule hoare_pre)
    apply ((wp whenE_throwError_wp check_vp_wpR hoare_vcg_const_imp_lift_R
                   create_mapping_entries_parent_for_refs
                   find_vspace_for_asid_lookup_vspace_wp
                | wpc
                | simp add: valid_arch_inv_def valid_page_inv_def
                | (simp add: cte_wp_at_caps_of_state,
                   wp create_mapping_entries_same_refs_ex hoare_vcg_ex_lift_R))+)[1]
   apply (clarsimp simp: valid_cap_simps cap_aligned_def neq_Nil_conv)
   apply (frule diminished_cte_wp_at_valid_cap[where p="(a, b)" for a b], clarsimp)
   apply (clarsimp simp: cte_wp_at_caps_of_state mask_cap_def
                         diminished_def[where cap="ArchObjectCap (PageCap d x y t z w)" for d x y t z w])
   apply (clarsimp simp: cap_rights_update_def acap_rights_update_def
                  split: cap.splits arch_cap.splits)
   apply (cases slot,
              auto simp: vmsz_aligned_def mask_def
                         valid_arch_caps_def cte_wp_at_caps_of_state
                         neq_Nil_conv invs_def valid_state_def
                         valid_cap_def cap_aligned_def data_at_def bit_simps
                  split: if_splits,
              fastforce+)[1]
  apply (cases "invocation_type label = ArchInvocationLabel RISCVPageUnmap")
   apply (simp split del: if_split)
   apply (rule hoare_pre, wp)
   apply (clarsimp simp: valid_arch_inv_def valid_page_inv_def)
   apply (thin_tac "Ball S P" for S P)
   apply (rule conjI)
    apply (clarsimp split: option.split)
    apply (clarsimp simp: valid_cap_simps cap_aligned_def)
    apply (simp add: valid_unmap_def)
   apply (erule cte_wp_at_weakenE)
   apply (clarsimp simp: is_arch_diminished_def is_cap_simps)
  apply (cases "invocation_type label = ArchInvocationLabel RISCVPageGetAddress";
             simp split del: if_split;
             wpsimp simp: valid_arch_inv_def valid_page_inv_def)
  done *)

lemma decode_page_table_invocation_wf[wp]:
  "arch_cap = PageTableCap pt_ptr pt_map_data \<Longrightarrow>
   \<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at (diminished (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (diminished (fst x)) (snd x) s)\<rbrace>
    decode_page_table_invocation label args slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  sorry (* FIXME RISCV
  apply (simp add: arch_decode_invocation_def decode_page_table_invocation_def
                   Let_def split_def is_final_cap_def
             cong: if_cong split del: if_split)
  apply ((wp whenE_throwError_wp lookup_pd_slot_wp find_vspace_for_asid_lookup_vspace_wp
             get_pde_wp
           | wpc
           | simp add: valid_arch_inv_def valid_pti_def unlessE_whenE vs_cap_ref_def
                 split del: if_split)+)[1]
  apply (rule conjI; clarsimp simp: is_arch_diminished_def is_cap_simps
                                elim!: cte_wp_at_weakenE)
  apply (rule conjI; clarsimp)
  apply (drule_tac x=ref in spec; erule impE; clarsimp)
   apply (fastforce elim!: is_aligned_pml4)
  apply (frule valid_arch_cap_typ_at; clarsimp)
  apply (strengthen not_in_global_refs_vs_lookup, rule conjI, fastforce)
  apply (clarsimp simp: neq_Nil_conv)
  apply (thin_tac "Ball S P" for S P)
  apply (clarsimp simp: cte_wp_at_caps_of_state diminished_table_cap_simps valid_vm_rights_def
                           is_arch_update_def cap_master_cap_def is_cap_simps)
  apply (rule conjI)
   apply (frule_tac p="(aa,b)" in valid_capsD[OF _ valid_objs_caps], fastforce,
          clarsimp simp: valid_cap_simps cap_aligned_def order_le_less_trans[OF word_and_le2])
  apply (frule empty_table_pt_capI; clarsimp)
  apply (clarsimp simp: vspace_at_asid_def; drule (2) vs_lookup_invs_ref_is_unique; clarsimp)
  apply (clarsimp simp: get_pd_index_def get_pdpt_index_def get_pml4_index_def)
  apply (rule conjI[rotated], simp add: bit_simps mask_def, word_bitwise)
  apply (erule rsubst[where P="\<lambda>r. (r \<rhd> p) s" for p s])
  apply (clarsimp simp: mask_def bit_simps; word_bitwise)
  done *)

lemma cte_wp_at_eq_simp:
  "cte_wp_at ((=) cap) = cte_wp_at (\<lambda>c. c = cap)"
  apply (rule arg_cong [where f=cte_wp_at])
  apply force
  done

lemma arch_decode_inv_wf[wp]:
  "\<lbrace>invs and valid_cap (ArchObjectCap arch_cap) and
    cte_wp_at (diminished (ArchObjectCap arch_cap)) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at (diminished (fst x)) (snd x) s) and
    (\<lambda>s. \<forall>x \<in> set excaps. s \<turnstile> (fst x))\<rbrace>
     arch_decode_invocation label args x_slot slot arch_cap excaps
   \<lbrace>valid_arch_inv\<rbrace>,-"
  sorry (* FIXME RISCV
  apply (cases arch_cap)
         (* ASIDPoolCap \<rightarrow> RISCVASIDPoolAssign *)
          apply (rename_tac word1 word2)
          apply (simp add: arch_decode_invocation_def Let_def split_def
                     cong: if_cong split del: if_split)
          apply (rule hoare_pre)
           apply ((wp whenE_throwError_wp check_vp_wpR ensure_empty_stronger select_wp select_ext_weak_wp
                  | wpc | simp add: valid_arch_inv_def valid_apinv_def)+)[1]
          apply (simp add: valid_arch_inv_def valid_apinv_def)
          apply (intro allI impI ballI)
          apply (elim conjE exE)
          apply simp
          apply (clarsimp simp: dom_def neq_Nil_conv)
          apply (thin_tac "Ball S P" for S P)+
          apply (clarsimp simp: valid_cap_def)
          apply (rule conjI)
           apply (clarsimp simp: obj_at_def)
          apply (subgoal_tac "asid_low_bits_of (ucast xa + word2) = xa")
            apply simp
           apply (simp add: is_aligned_nth)
           apply (subst word_plus_and_or_coroll)
            apply (rule word_eqI)
            apply (clarsimp simp: word_size word_bits_def nth_ucast)
            apply (drule test_bit_size)
            apply (simp add: word_size asid_low_bits_def)
           apply (rule word_eqI)
          apply (clarsimp simp: asid_bits_of_defs asid_bits_defs word_size word_bits_def nth_ucast)
          apply (rule conjI)
           apply (clarsimp simp add: cte_wp_at_caps_of_state)
           apply (rename_tac c c')
           apply (frule_tac cap=c' in caps_of_state_valid, assumption)
           apply (drule (1) diminished_is_update)
           apply (clarsimp simp: is_pml4_cap_def cap_rights_update_def acap_rights_update_def)
         apply (clarsimp simp: word_neq_0_conv asid_high_bits_of_def)
         apply (drule vs_lookup_atI, erule_tac s="word2 >> asid_low_bits" in rsubst)
         apply (simp add: asid_bits_defs aligned_shift[OF ucast_less[where 'b=9], simplified])
        (* ASIDControlCap \<rightarrow> RISCVASIDControlMakePool *)
         apply (simp add: arch_decode_invocation_def Let_def split_def
                   cong: if_cong split del: if_split)
         apply (rule hoare_pre)
          apply ((wp whenE_throwError_wp check_vp_wpR ensure_empty_stronger
                 | wpc | simp add: valid_arch_inv_def valid_aci_def is_aligned_shiftl_self)+)[1]
                 apply (rule_tac Q'= "\<lambda>rv. real_cte_at rv
                                            and ex_cte_cap_wp_to is_cnode_cap rv
                                            and (\<lambda>s. descendants_of (snd (excaps!0)) (cdt s) = {})
                                            and cte_wp_at (\<lambda>c. \<exists>idx. c = UntypedCap False frame pageBits idx) (snd (excaps!0))
                                            and (\<lambda>s. riscv_asid_table (arch_state s) free = None)"
                         in hoare_post_imp_R)
                  apply (simp add: lookup_target_slot_def)
                  apply wp
                 apply (clarsimp simp: cte_wp_at_def)
                apply (wp ensure_no_children_sp select_ext_weak_wp select_wp whenE_throwError_wp | wpc | simp)+
         apply clarsimp
         apply (rule conjI, fastforce)
         apply (cases excaps, simp)
         apply (case_tac list, simp)
         apply clarsimp
         apply (rule conjI)
          apply clarsimp
          apply (simp add: ex_cte_cap_wp_to_def)
          apply (rule_tac x=ac in exI)
          apply (rule_tac x=ba in exI)
          apply (clarsimp simp add: cte_wp_at_caps_of_state)
          apply (drule (1) caps_of_state_valid[rotated])+
          apply (drule (1) diminished_is_update)+
          apply (clarsimp simp: is_cap_simps cap_rights_update_def)
         apply (clarsimp simp add: cte_wp_at_caps_of_state)
         apply (drule (1) caps_of_state_valid[rotated])+
         apply (drule (1) diminished_is_update)+
         apply (clarsimp simp: cap_rights_update_def)
      (* PageCap *)
      apply (simp add: arch_decode_invocation_def)
      apply (wp, simp, simp)
     (* PageTableCap *)
     apply (simp add: arch_decode_invocation_def)
     apply (wp, simp, simp)
  done *)

declare word_less_sub_le [simp]

crunch pred_tcb_at [wp]:
  perform_page_table_invocation, perform_page_invocation, perform_asid_pool_invocation
  "pred_tcb_at proj P t"
  (wp: crunch_wps simp: crunch_simps)

lemma arch_pinv_st_tcb_at:
  "\<lbrace>invs and valid_arch_inv ai and ct_active and
    st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t\<rbrace>
     arch_perform_invocation ai
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases ai; simp add: arch_perform_invocation_def valid_arch_inv_def)
  apply (wp perform_asid_control_invocation_st_tcb_at; fastforce elim!: pred_tcb_weakenE)+
  done

lemma get_cap_diminished:
  "\<lbrace>valid_objs\<rbrace> get_cap slot \<lbrace>\<lambda>cap. cte_wp_at (diminished cap) slot\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state diminished_def mask_cap_def)
  apply (frule (1) caps_of_state_valid_cap)
  apply (rule exI[of _ "UNIV"])
  apply simp
  done

end


context begin interpretation Arch .

requalify_consts
  valid_arch_inv

requalify_facts
  invoke_arch_tcb
  invoke_arch_invs
  sts_valid_arch_inv
  arch_decode_inv_wf
  arch_pinv_st_tcb_at
  get_cap_diminished

end

declare invoke_arch_invs[wp]
declare arch_decode_inv_wf[wp]

end
