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
Lemmas on arch get/set object etc
*)

theory ArchAcc_AI
imports "../SubMonad_AI" "Lib.Crunch_Instances_NonDet"
begin

context non_vspace_op
begin

(* FIXME RISCV: arch split/move to arch (level) *)
lemma valid_vso_at[wp]:"\<lbrace>valid_vso_at level p\<rbrace> f \<lbrace>\<lambda>_. valid_vso_at level p\<rbrace>"
  by (rule valid_vso_at_lift_aobj_at; wp vsobj_at; simp)

end

context Arch begin global_naming RISCV64


(* FIXME RISCV: move up *)
(* Is there a lookup that leads to a page table at (level, p)? *)
locale_abbrev ex_vs_lookup_table ::
  "vm_level \<times> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd>") where
  "ex_vs_lookup_table \<equiv>
     \<lambda>(level,p) s. \<exists>asid vref.
       vs_lookup_table level asid vref s = Some (level, p) \<and> vref \<in> user_region s"

bundle unfold_objects =
  obj_at_def[simp]
  kernel_object.splits[split]
  arch_kernel_obj.splits[split]
  get_object_wp [wp]

bundle unfold_objects_asm =
  obj_at_def[simp]
  kernel_object.split_asm[split]
  arch_kernel_obj.split_asm[split]

lemma vs_lookup_table_target:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   vs_lookup_target (level + 1) asid (vref_for_level vref (level + 1)) s = Some (level + 1, p)"
  apply (simp add: vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def obind_assoc)
  apply (subgoal_tac "level \<noteq> asid_pool_level"; clarsimp)
  apply (cases "level = max_pt_level", clarsimp simp: max_pt_level_plus_one in_omonad)
  apply (subgoal_tac "level + 1 \<noteq> asid_pool_level")
   prefer 2
   apply (metis max_pt_level_plus_one add.right_cancel)
  apply (clarsimp simp: obind_assoc simp del: asid_pool_level_neq)
  apply (subst (asm) pt_walk_split_Some[where level'="level + 1"]; simp add: less_imp_le)
  apply (subst (asm) (2) pt_walk.simps)
  apply (subgoal_tac "level + 1 \<noteq> asid_pool_level")
   prefer 2
   apply (metis max_pt_level_plus_one add.right_cancel)
  apply (clarsimp simp: in_omonad simp del: asid_pool_level_neq cong: conj_cong)
  apply (rule_tac x="level + 1" in exI)
  apply (subst pt_walk_vref_for_level; simp add: less_imp_le)
  apply (clarsimp simp: is_PageTablePTE_def pptr_from_pte_def split: if_split_asm)
  done

lemma valid_vs_lookupD:
  "\<lbrakk> vs_lookup_target bot_level asid vref s = Some (level, p) ;
     vref \<in> user_region s ; valid_vs_lookup s \<rbrakk>
   \<Longrightarrow>  asid \<noteq> 0
        \<and> (\<exists>p' cap. caps_of_state s p' = Some cap \<and> obj_refs cap = {p}
                    \<and> vs_cap_ref cap = Some (asid_for_level asid level, vref_for_level vref level))"
  unfolding valid_vs_lookup_def
  by auto

lemma unique_table_refsD:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     unique_table_refs s; obj_refs cap' = obj_refs cap \<rbrakk>
   \<Longrightarrow> table_cap_ref cap' = table_cap_ref cap"
  unfolding unique_table_refs_def by blast

lemma table_cap_ref_vs_cap_ref:
  "\<lbrakk> table_cap_ref cap' = table_cap_ref cap; is_pt_cap cap; is_pt_cap cap' \<rbrakk>
   \<Longrightarrow> vs_cap_ref cap' = vs_cap_ref cap"
  apply (clarsimp simp: table_cap_ref_def vs_cap_ref_def arch_cap_fun_lift_def split: cap.splits)
  apply (clarsimp simp: vs_cap_ref_arch_def table_cap_ref_arch_def split: arch_cap.splits)
  done

(* FIXME RISCV: probably need extra lemma for asid_pool_level *)
lemma unique_vs_lookup_table:
  "\<lbrakk> unique_table_refs s; valid_vs_lookup s; valid_uses s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s;
     vs_lookup_table level asid vref s = Some (level, p); vref \<in> user_region s;
     vs_lookup_table level' asid' vref' s = Some (level', p'); vref' \<in> user_region s;
     p' = p; level \<le> max_pt_level; level' \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> asid_for_level asid' (level'+1) = asid_for_level asid (level+1) \<and>
       vref_for_level vref' (level'+1) = vref_for_level vref (level+1)"
  apply (frule (6) valid_vspace_objs_strongD)
  apply (frule (6) valid_vspace_objs_strongD[where pt_ptr=p'])
  apply (drule (1) vs_lookup_table_target)+
  apply (drule valid_vs_lookupD, erule (1) vref_for_level_user_region, assumption)+
  apply (elim conjE exE)
  apply (rename_tac pt pt' cptr cptr' cap cap')
  apply (drule (2) unique_table_refsD, simp)
  apply (subgoal_tac "is_pt_cap cap \<and> is_pt_cap cap'")
   apply (drule table_cap_ref_vs_cap_ref; simp)
   apply clarsimp
  sorry

lemma
  "\<lbrakk> vs_lookup_table level asid (vref_for_level vref (level+1)) s = Some (level, p);
     vs_lookup_table level' asid (vref_for_level vref' (level'+1)) s = Some (level', p);
     vref_for_level vref' (level'+1) = vref_for_level vref (level+1);
     vref \<in> user_region s; level' < level; level \<le> max_pt_level \<rbrakk>
   \<Longrightarrow> \<exists>vref'' p' pte. vs_lookup_slot 0 asid vref'' s = Some (0, p') \<and> ptes_of s p' = Some pte \<and>
                       is_PageTablePTE pte"
  oops

lemma no_loop_vs_lookup_table: (* FIXME RISCV *)
  "\<lbrakk> unique_table_refs s; valid_vs_lookup s; valid_uses s;
     valid_vspace_objs s; valid_asid_table s; pspace_aligned s;
     valid_caps (caps_of_state s) s;
     vs_lookup_table level asid (vref_for_level vref (level+1)) s = Some (level, p);
     vs_lookup_table level' asid (vref_for_level vref' (level'+1)) s = Some (level', p);
     vref_for_level vref' (level'+1) = vref_for_level vref (level+1);
     vref \<in> user_region s; level \<le> max_pt_level; level' \<le> max_pt_level \<rbrakk>
    \<Longrightarrow> level' = level"
  sorry

lemma ex_vs_lookup_level:
  "\<lbrakk> \<exists>\<rhd> (level, p) s;  \<exists>\<rhd> (level', p) s \<rbrakk> \<Longrightarrow> level' = level"
  apply clarsimp
  oops (* FIXME RISCV: add assumptions, use previous lemmas *)

lemma get_asid_pool_wp [wp]:
  "\<lbrace>\<lambda>s. \<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> Q pool s\<rbrace>
  get_asid_pool p
  \<lbrace>Q\<rbrace>"
  by (wpsimp simp: obj_at_def in_opt_map_eq)


lemma set_asid_pool_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def wp: set_object_wp)

lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]

bundle pagebits =
  pt_bits_def[simp]
  pageBits_def[simp] mask_lower_twice[simp]
  word_bool_alg.conj_assoc[symmetric,simp] obj_at_def[simp]
  pte.splits[split]


lemma get_pt_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) p s \<longrightarrow> Q pt s\<rbrace> get_pt p \<lbrace>Q\<rbrace>"
  by (wpsimp simp: obj_at_def in_opt_map_eq)


lemma get_pte_wp:
  "\<lbrace>\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~mask pt_bits) s \<longrightarrow>
        Q (pt (ucast (p && mask pt_bits >> pte_bits))) s\<rbrace>
  get_pte p
  \<lbrace>Q\<rbrace>"
  by (wpsimp simp: ptes_of_Some in_opt_map_eq obj_at_def)

lemma get_pte_inv[wp]:
  "\<lbrace>P\<rbrace> get_pte p \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp wp: get_pte_wp)

lemmas store_pte_typ_ats [wp] = abs_typ_at_lifts [OF store_pte_typ_at]

crunch cte_wp_at[wp]: set_irq_state "\<lambda>s. P (cte_wp_at P' p s)"

lemma set_pt_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_pt ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_pt_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
               simp: cte_wp_at_after_update)

lemma set_asid_pool_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_asid_pool ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

lemma set_pt_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_pt ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done


lemma set_asid_pool_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done

lemma mask_pt_bits_inner_beauty:
  "is_aligned p pte_bits \<Longrightarrow>
  (p && ~~ mask pt_bits) + (ucast ((ucast (p && mask pt_bits >> pte_bits))::pt_index) << pte_bits) = (p::machine_word)"
  by (rule mask_split_aligned; simp add: bit_simps)

lemma more_pt_inner_beauty:
  fixes x :: pt_index
  fixes p :: machine_word
  assumes x: "x \<noteq> ucast (p && mask pt_bits >> pte_bits)"
  shows "(p && ~~ mask pt_bits) + (ucast x << pte_bits) = p \<Longrightarrow> False"
  by (rule mask_split_aligned_neg[OF _ _ x]; simp add: bit_simps)


lemmas undefined_validE_R = hoare_FalseE_R[where f=undefined]


lemma arch_derive_cap_valid_cap:
  "\<lbrace>valid_cap (cap.ArchObjectCap arch_cap)\<rbrace>
  arch_derive_cap arch_cap
  \<lbrace>valid_cap\<rbrace>, -"
  apply(simp add: arch_derive_cap_def)
  apply(cases arch_cap, simp_all add: arch_derive_cap_def o_def)
      apply(rule hoare_pre, wpc?, wp+;
            clarsimp simp add: cap_aligned_def valid_cap_def split: option.splits)+
  done


lemma arch_derive_cap_inv:
  "\<lbrace>P\<rbrace> arch_derive_cap arch_cap \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding arch_derive_cap_def by (cases arch_cap; wpsimp)

definition
  "valid_mapping_entries m \<equiv> case m of
    (InvalidPTE, _) \<Rightarrow> \<top>
  | (PagePTE _ _ _, p) \<Rightarrow> pte_at p
  | (PageTablePTE _ _, _) \<Rightarrow> \<bottom>"

definition
  "invalid_pte_at p \<equiv> \<lambda>s. ptes_of s p = Some InvalidPTE"

(* FIXME RISCV: \<forall>level might not be quite right, we'll have to see *)
definition
  "valid_slots \<equiv> \<lambda>(pte, p) s. wellformed_pte pte \<and>
     (\<forall>level. \<exists>\<rhd>(level, p && ~~ mask pt_bits) s \<longrightarrow> pte_at p s \<and> valid_pte level pte s)"


lemma ucast_mask_asid_low_bits [simp]:
  "ucast ((asid::machine_word) && mask asid_low_bits) = (ucast asid :: asid_low_index)"
  by word_eqI_solve


lemma ucast_ucast_asid_high_bits [simp]:
  "ucast (ucast (asid_high_bits_of asid)::machine_word) = asid_high_bits_of asid"
  by word_eqI_solve


lemma mask_asid_low_bits_ucast_ucast:
  "((asid::machine_word) && mask asid_low_bits) = ucast (ucast asid :: asid_low_index)"
  by word_eqI_solve


lemma set_asid_pool_cur [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: get_object_wp)


lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wp)


crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)

lemma set_asid_pool_pts_of [wp]:
  "set_asid_pool p a \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  unfolding set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (erule_tac P=P in subst[rotated])
  apply (rule ext)
  apply (clarsimp simp: opt_map_def obj_at_def split: option.splits)
  done

lemma set_asid_pool_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_arch; wp set_asid_pool_typ_at)

lemma set_asid_pool_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def)


lemma invs_valid_global_arch_objs:
  "invs s \<Longrightarrow> valid_global_arch_objs s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_state_def)

lemma is_aligned_pt:
  "\<lbrakk> pt_at pt s; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned pt pt_bits"
  apply (clarsimp simp: obj_at_def)
  apply (drule(1) pspace_alignedD)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma is_aligned_global_pt:
  "\<lbrakk>pt \<in> riscv_global_pts (arch_state s) level; pspace_aligned s; valid_arch_state s\<rbrakk>
   \<Longrightarrow> is_aligned pt pt_bits"
  by (fastforce simp: valid_arch_state_def valid_global_arch_objs_def intro: is_aligned_pt)

lemma page_table_pte_atI:
  "\<lbrakk> pt_at p s; x < 2^(pt_bits - pte_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at (p + (x << pte_bits)) s"
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                 split: kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self word_bits_conv bit_simps)
  apply (subgoal_tac "p = (p + (x << pte_bits) && ~~ mask pt_bits)")
   subgoal by (auto simp: bit_simps)
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: bit_simps)
  apply simp
  apply (subst upper_bits_unset_is_l2p_64[unfolded word_bits_conv])
   apply (simp add: bit_simps)
  apply (rule shiftl_less_t2n)
   apply (simp add: bit_simps)
  apply (simp add: bit_simps)
  done

lemma page_table_pte_at_diffE:
  "\<lbrakk> pt_at p s; q - p = x << pte_bits;
    x < 2^(pt_bits - pte_bits); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at q s"
  apply (clarsimp simp: diff_eq_eq add.commute)
  apply (erule(2) page_table_pte_atI)
  done

lemma vs_lookup_table_extend:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt);
    pt_walk level bot_level pt vref (ptes_of s) = Some (bot_level, p);
    level \<le> max_pt_level\<rbrakk>
   \<Longrightarrow> vs_lookup_table bot_level asid vref s = Some (bot_level, p)"
  by (rule vs_lookup_split_Some[THEN iffD2] ; fastforce intro!: pt_walk_max_level)

lemma pt_walk_pt_at:
  "\<lbrakk> pt_walk level bot_level pt_ptr vptr (ptes_of s) = Some (level', p);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vptr \<in> user_region s; valid_vspace_objs s; valid_uses s; valid_asid_table s; pspace_aligned s \<rbrakk>
   \<Longrightarrow> pt_at p s"
  apply (drule pt_walk_level)
  apply (frule pt_walk_max_level)
  apply (drule vs_lookup_table_extend ; assumption?)
  apply (fastforce dest!: valid_vspace_objs_strongD simp: pt_at_eq)
  done

lemma pt_lookup_slot_from_level_pte_at:
  "\<lbrakk> pt_lookup_slot_from_level level bot_level pt_ptr vptr (ptes_of s) = Some (level', p);
     vs_lookup_table level asid vptr s = Some (level, pt_ptr); level \<le> max_pt_level;
     vref \<in> user_region s; valid_uses s; valid_asid_table s; pspace_aligned s \<rbrakk>
  \<Longrightarrow> pte_at p s"
  unfolding pt_lookup_slot_from_level_def
  apply (simp add: oreturn_def obind_def split: option.splits)

  sorry (* FIXME RISCV *)  (* should follow from above + offset calculation *)

lemma set_pt_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_distinct get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                split: kernel_object.splits arch_kernel_obj.splits)
  done

crunches store_pte
  for arch[wp]: "\<lambda>s. P (arch_state s)"
  and "distinct"[wp]: pspace_distinct

lemma store_pt_asid_pools_of[wp]:
  "set_pt p pt \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (auto simp: obj_at_def opt_map_def elim!: rsubst[where P=P])
  done

lemma store_pte_asid_pools_of[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding store_pte_def by wpsimp

lemma store_pte_vspace_at_asid:
  "store_pte p pte \<lbrace>vspace_at_asid asid pt\<rbrace>"
  unfolding vspace_at_asid_def by (wp vspace_for_asid_lift)

(* FIXME MOVE *)
lemma ko_at_kheap:
  "ko_at ko p s \<Longrightarrow> kheap s p = Some ko"
  unfolding obj_at_def by simp

lemma store_pte_valid_objs [wp]:
  "\<lbrace>(\<lambda>s. wellformed_pte pte) and valid_objs\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def bind_assoc set_object_def get_object_def)
  apply (wpsimp simp_del: fun_upd_apply)
  apply (clarsimp simp: valid_objs_def dom_def simp del: fun_upd_apply)
  apply (frule ko_at_kheap)
  apply (fastforce intro!: valid_obj_same_type simp: valid_obj_def split: if_split_asm)
  done

lemma set_pt_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_pt_def get_object_def bind_assoc set_object_def)
  apply (wpsimp)
  apply (subst caps_of_state_after_update, auto elim: obj_at_weakenE)
  done

lemma store_pte_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> store_pte pt p \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp set_object_aligned get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_aligned|wpc)+
  including unfold_objects
  apply clarsimp
  done

lemma set_asid_pool_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_distinct|wpc)+
  including unfold_objects
  apply clarsimp
  done


lemma store_pte_valid_pte [wp]:
  "\<lbrace>valid_pte level pt\<rbrace> store_pte p pte \<lbrace>\<lambda>_. valid_pte level pt\<rbrace>"
  by (wp valid_pte_lift store_pte_typ_at)

lemma global_refs_kheap [simp]:
  "global_refs (kheap_update f s) = global_refs s"
  by (simp add: global_refs_def)


lemma set_pt_valid_objs:
  "\<lbrace>(\<lambda>s. \<forall>i. wellformed_pte (pt i)) and valid_objs\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_valid_objs)
  apply (clarsimp simp: valid_obj_def obj_at_def split: kernel_object.splits arch_kernel_obj.splits)
  done


lemma set_pt_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp simp: set_pt_def live_def hyp_live_def arch_live_def wp: get_object_wp set_object_iflive)


lemma set_pt_zombies:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  unfolding set_pt_def including unfold_objects
  by (wpsimp wp: get_object_wp)


lemma set_pt_zombies_state_refs:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  unfolding set_pt_def set_object_def including unfold_objects
  apply wpsimp
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: state_refs_of_def split: option.splits)
  done

lemma set_pt_zombies_state_hyp_refs:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def split: option.splits)
  done

lemma set_pt_cdt:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_pt_def including unfold_objects by wpsimp


lemma set_pt_valid_mdb:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: set_pt_cdt valid_mdb_lift simp: set_pt_def set_object_def)

lemma set_pt_valid_idle:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_pt_def)

lemma set_pt_ifunsafe:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects by (wpsimp simp: set_pt_def)

lemma set_pt_reply_caps:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace> set_pt p pt \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

lemma set_pt_reply_masters:
  "\<lbrace>valid_reply_masters\<rbrace>  set_pt p pt  \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


crunch global_ref [wp]: set_pt "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch arch [wp]: set_pt "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)


crunch idle [wp]: set_pt "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_pt "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)


lemma set_pt_valid_global:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

lemma set_pt_cur:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace>
  set_pt p pt
  \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def is_tcb_def)
  done


lemma set_pt_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_pt p pt \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp get_object_wp set_object_aligned)
  apply (clarsimp simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)
  done


crunch interrupt_states[wp]: set_pt "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma unique_table_caps_ptD:
  "\<lbrakk> cs p = Some cap; vs_cap_ref cap = None;
     cs p' = Some cap'; is_pt_cap cap; is_pt_cap cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps_2 cs\<rbrakk>
  \<Longrightarrow> p = p'"
  unfolding unique_table_caps_2_def by fastforce


lemma valid_objs_caps:
  "valid_objs s \<Longrightarrow> valid_caps (caps_of_state s) s"
  apply (clarsimp simp: valid_caps_def)
  apply (erule (1) caps_of_state_valid_cap)
  done

lemma set_pt_table_caps[wp]:
  "\<lbrace>valid_table_caps and (\<lambda>s. valid_caps (caps_of_state s) s) and
    (\<lambda>s. ((\<exists>slot. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
                  pt = empty_pt) \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p (Some asid)))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def set_pt_def
  apply (wp set_object_wp)
  sorry (* FIXME RISCV *)


lemma set_object_caps_of_state:
  "\<lbrace>(\<lambda>s. \<not>tcb_at p s \<and> \<not>(\<exists>n. cap_table_at n p s)) and
    K ((\<forall>x y. obj \<noteq> CNode x y) \<and> (\<forall>x. obj \<noteq> TCB x)) and
    (\<lambda>s. P (caps_of_state s))\<rbrace>
   set_object p obj
   \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (clarsimp simp: set_object_def)
  apply wp
  apply clarify
  apply (erule rsubst[where P=P])
  apply (rule ext)
  apply (simp add: caps_of_state_cte_wp_at obj_at_def is_cap_table_def
                   is_tcb_def)
  apply (auto simp: cte_wp_at_cases)
  done


lemma set_pt_valid_vspace_objs[wp]:
  "\<lbrace>\<lambda>s. valid_vspace_objs s \<and>
        (\<forall>level. (\<exists>\<rhd> (level,p)) s \<longrightarrow>
           (\<forall>i\<in>if level = max_pt_level then - kernel_mapping_slots else UNIV. valid_pte level (pt i) s))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding set_pt_def
  apply (wp set_object_wp)
  sorry (* FIXME RISCV
  apply (clarsimp simp: valid_vspace_objs_def)
  *)


(* FIXME RISCV: assumption is potentially missing something about asid \<noteq> 0 *)
lemma set_pt_valid_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. valid_vs_lookup s \<and> valid_arch_state s \<and>
        valid_vspace_objs s \<and>
        (\<forall>level. (\<exists>\<rhd> (level,p)) s \<longrightarrow> (\<forall>x. valid_pte level (pt x) s)) \<and>
        (\<forall>level' asid vref. vs_lookup_target level' asid vref s = Some (level', p) \<longrightarrow>
            (\<forall>x p. pte_ref (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                              p \<in> obj_refs cap \<and>
                              vs_cap_ref cap = Some (asid, vref))))\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  sorry (* FIXME RISCV
  using set_pt_valid_vspace_objs[of p pt] set_pt_valid_arch_state[of p pt]
  apply (clarsimp simp: valid_def simpler_set_pt_def)
  apply (drule_tac x=s in spec)+
  apply (clarsimp simp: valid_vs_lookup_def  split: if_split_asm)
  apply (erule (1) vs_lookup_pagesE_alt)
      apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                            fun_upd_def)
     apply (drule_tac x=pa in spec)
     apply (drule_tac x="[VSRef (ucast a) None]" in spec)+
     apply simp
     apply (drule vs_lookup_pages_atI)
     apply simp
     apply (subst caps_of_state_after_update, simp add: obj_at_def)
     apply simp
    apply (drule_tac x=pa in spec)
    apply (drule_tac x="[VSRef (ucast b) (Some AASIDPool),
                         VSRef (ucast a) None]" in spec)+
    apply simp
    apply (drule vs_lookup_pages_apI)
      apply (simp split: if_split_asm)
     apply simp+
    apply (subst caps_of_state_after_update, simp add: obj_at_def)
    apply simp
   apply (drule_tac x=pa in spec)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)+
   apply simp
   apply (drule vs_lookup_pages_pdI)
        apply (simp split: if_split_asm)+
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply fastforce
  apply (clarsimp simp: fun_upd_def  split: if_split_asm)
   apply (thin_tac "valid_vspace_objs s" for s, thin_tac "valid_arch_state s" for s)
   apply (subst caps_of_state_after_update, simp add: obj_at_def)
   apply (thin_tac "\<forall>p ref. P p ref" for P)
   apply (drule_tac x="[VSRef (ucast c) (Some APageDirectory),
                        VSRef (ucast b) (Some AASIDPool),
                        VSRef (ucast a) None]" in spec)
   apply (thin_tac "valid_pte pte s" for pte s)
   apply (erule impE, fastforce intro: vs_lookup_pdI)
   apply (drule_tac x=d in spec)
   apply (erule impE)
    apply (erule (5) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
   apply (drule spec, drule spec, erule impE, assumption)
   apply assumption
  apply (thin_tac "valid_vspace_objs s" for s, thin_tac "valid_arch_state s" for s)
  apply (subst caps_of_state_after_update, simp add: obj_at_def)
  apply (thin_tac "\<forall>ref. (ref \<unrhd> p) s \<longrightarrow> P ref" for P)
  apply (drule_tac x=pa in spec)
  apply (drule_tac x="[VSRef (ucast d) (Some APageTable),
                       VSRef (ucast c) (Some APageDirectory),
                       VSRef (ucast b) (Some AASIDPool),
                       VSRef (ucast a) None]" in spec)
  apply (thin_tac "(\<exists>\<rhd> p) s \<longrightarrow> P" for P)
  apply (erule impE, fastforce intro: vs_lookup_pages_ptI)
  apply simp
  done *)

lemma set_pt_asid_pool_caps[wp]:
  "set_pt p pt \<lbrace>valid_asid_pool_caps\<rbrace>"
  unfolding valid_asid_pool_caps_def
  by (rule hoare_lift_Pf[where f=caps_of_state]; wp)

lemma set_pt_arch_caps [wp]:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_vspace_objs and
    (\<lambda>s. valid_caps (caps_of_state s) s \<and>
         ((\<exists>slot. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p None))) \<longrightarrow>
          pt = empty_pt \<or>
         (\<forall>slot. \<exists>asid. caps_of_state s slot =
           Some (ArchObjectCap (PageTableCap p (Some asid))))) \<and>
         (\<forall>level. (\<exists>\<rhd> (level,p)) s \<longrightarrow> (\<forall>x. valid_pte level (pt x) s)) \<and>
         (\<forall>level' asid vref. vs_lookup_target level' asid vref s = Some (level', p) \<longrightarrow>
            (\<forall>x p. pte_ref (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                              p \<in> obj_refs cap \<and>
                              vs_cap_ref cap = Some (asid, vref)))))\<rbrace>
  set_pt p pt \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (wp set_pt_valid_vs_lookup)
  apply clarsimp
  done


lemma valid_global_refsD2:
  "\<lbrakk> caps_of_state s ptr = Some cap; valid_global_refs s \<rbrakk>
      \<Longrightarrow> global_refs s \<inter> cap_range cap = {}"
  by (cases ptr,
      simp add: valid_global_refs_def valid_refs_def
                cte_wp_at_caps_of_state)


lemma valid_global_refsD:
  "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s;
         r \<in> global_refs s \<rbrakk>
        \<Longrightarrow> r \<notin> cap_range cap"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) valid_global_refsD2)
  apply fastforce
  done


lemma set_pt_global_objs [wp]:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def by wp


crunch v_ker_map[wp]: set_pt "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_pt_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def vspace_at_asid_def)
  apply (rule hoare_lift_Pf2 [where f="arch_state"])
   apply wp+
  done

lemma set_pt_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_pt p pt \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)

lemma pts_of_upd_id:
  "obj_ref \<noteq> pt_ptr \<Longrightarrow> pts_of (s\<lparr> kheap := (kheap s)(obj_ref := Some ko)\<rparr>) pt_ptr = pts_of s pt_ptr"
  unfolding pt_of_def
  by (clarsimp simp: opt_map_def split: option.splits)

lemma pt_walk_eqI:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pts' pt_ptr' = pts pt_ptr' \<and> is_aligned pt_ptr' pt_bits \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts')
      = pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  apply (induct top_level arbitrary: pt_ptr; clarsimp?)
   apply (simp add: pt_walk.simps)
  apply (subst pt_walk.simps)
  apply (subst (2) pt_walk.simps)
  apply clarsimp
  apply (rule obind_eqI)
   apply (simp (no_asm) add: pte_of_def)
   apply (fastforce simp: obind_def split: option.split)
  apply clarsimp
  apply (rename_tac pte)
  apply (drule_tac x="pptr_from_pte pte" in meta_spec)
  apply (erule meta_impE; assumption?)
  apply clarsimp
  apply (subgoal_tac "is_aligned pt_ptr pt_bits \<and> pts' pt_ptr = pts pt_ptr")
   prefer 2
   subgoal by simp
  apply (erule_tac x=level' in allE, simp)
  apply (erule_tac x=pt_ptr' in allE)
  apply (erule impE; assumption?)
  apply (subst pt_walk.simps)
  apply (subgoal_tac "level' < top_level")
   prefer 2
   apply (fastforce dest!: pt_walk_max_level simp: le_less_trans)
  apply (fastforce simp: pte_of_def in_omonad)
  done

lemma pt_walk_pt_upd_id:
  "\<lbrakk> \<forall>level' pt_ptr'.
       level < level'
       \<longrightarrow> pt_walk top_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref \<and> is_aligned pt_ptr' pt_bits \<rbrakk>
   \<Longrightarrow> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p (pts(obj_ref := pt)))
      = pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  by (rule pt_walk_eqI; auto)

lemma pt_lookup_target_translate_address_upd_eq:
  "\<lbrakk> pt_lookup_target 0 pt_ptr vref ptes' = pt_lookup_target 0 pt_ptr vref ptes \<rbrakk>
   \<Longrightarrow> translate_address pt_ptr vref ptes' = translate_address pt_ptr vref ptes"
  unfolding translate_address_def
  by (simp add: obind_def split: option.splits)

lemma pt_lookup_target_slot_from_level_eq:
  "\<lbrakk> pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes'
     = pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes;
     \<And>level' slot. pt_lookup_slot_from_level max_pt_level level pt_ptr vref ptes = Some (level', slot)
                   \<Longrightarrow> (ptes' |> pte_ref) slot = (ptes |> pte_ref) slot \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vref ptes' = pt_lookup_target level pt_ptr vref ptes"
  unfolding pt_lookup_target_def
  by (fastforce simp: obind_def opt_map_def split: option.splits)

lemma pt_walk_Some_finds_pt:
  "\<lbrakk> pt_walk top_level level pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level, pt_ptr');
     level < top_level; is_aligned pt_ptr pt_bits \<rbrakk>
   \<Longrightarrow> pts pt_ptr \<noteq> None"
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp add: in_omonad split: if_splits)
  apply (fastforce simp: is_PageTablePTE_def pte_of_def in_omonad split: if_splits)
  done

lemma pte_of_pt_slot_offset_upd_id:
  "\<lbrakk> is_aligned pt_ptr pt_bits; obj_ref \<noteq> pt_ptr \<rbrakk>
   \<Longrightarrow> pte_of (pt_slot_offset level pt_ptr vptr) (pts(obj_ref := pt'))
      = pte_of (pt_slot_offset level pt_ptr vptr) pts"
  unfolding pte_of_def
  by (rule obind_eqI; clarsimp simp: in_omonad pt_slot_offset_id)+

lemma pt_lookup_target_pt_upd_eq:
  "\<lbrakk> \<forall>level' pt_ptr'.
       pt_walk max_pt_level level' pt_ptr vptr (\<lambda>p. pte_of p pts) = Some (level', pt_ptr')
       \<longrightarrow> pt_ptr' \<noteq> obj_ref \<and> is_aligned pt_ptr' pt_bits;
     obj_ref \<noteq> pt_ptr; is_aligned pt_ptr pt_bits; level \<le> max_pt_level; pt_at pt_ptr s \<rbrakk>
   \<Longrightarrow> pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p (pts(obj_ref := pt')))
      = pt_lookup_target level pt_ptr vptr (\<lambda>p. pte_of p pts)"
  apply (simp (no_asm) add: pt_lookup_target_def pt_lookup_slot_from_level_def obind_assoc)
  apply (subgoal_tac "pt_walk max_pt_level level pt_ptr vptr (\<lambda>p. pte_of p (pts(obj_ref := pt')))
                      = pt_walk max_pt_level level pt_ptr vptr (\<lambda>p. pte_of p pts)")
   prefer 2
   apply (rule pt_walk_pt_upd_id)
   apply (intro allI impI)
   apply (erule_tac x=level' in allE)
   apply fastforce
  apply (rule obind_eqI, assumption)
  apply (rule obind_eqI; clarsimp)
  apply (rule obind_eqI; clarsimp)
   apply (rename_tac level'' pt_ptr'')
   apply (drule sym)
   apply (frule pt_walk_level)
   apply (erule_tac x=level'' in allE)
   apply (erule_tac x=pt_ptr'' in allE)
   apply clarsimp
   apply (subst pte_of_pt_slot_offset_upd_id; clarsimp)
  apply (rule obind_eqI; clarsimp)
  done

lemma kheap_pt_upd_simp[simp]:
  "(kheap s(p \<mapsto> ArchObj (PageTable pt)) |> aobj_of |> pt_of)
   = (kheap s |> aobj_of |> pt_of)(p \<mapsto> pt)"
  unfolding aobj_of_def opt_map_def
  by (auto split: kernel_object.split)

lemma valid_global_tablesD:
  "\<lbrakk> valid_global_tables s;
     pt_walk max_pt_level bot_level (riscv_global_pt (arch_state s)) vref (ptes_of s)
     = Some (level, pt_ptr) \<rbrakk>
   \<Longrightarrow> vref \<in> kernel_regions s \<longrightarrow> pt_ptr \<in> riscv_global_pts (arch_state s) level"
  unfolding valid_global_tables_def by (simp add: Let_def riscv_global_pt_def)

lemma riscv_global_pt_aligned[simp]:
  "\<lbrakk> pspace_aligned s ; valid_global_arch_objs s \<rbrakk>
   \<Longrightarrow> is_aligned (riscv_global_pt (arch_state s)) pt_bits"
  apply (clarsimp simp add: valid_global_arch_objs_def)
  apply (rule is_aligned_pt; assumption?)
  apply (fastforce simp: riscv_global_pt_def)
  done

lemma riscv_global_pt_in_global_refs[simp]:
  "valid_global_arch_objs s \<Longrightarrow> riscv_global_pt (arch_state s) \<in> global_refs s"
  unfolding riscv_global_pt_def global_refs_def valid_global_arch_objs_def
  by fastforce

lemma kernel_regionsI:
  "p \<in> kernel_elf_window s \<Longrightarrow> p \<in> kernel_regions s"
  "p \<in> kernel_window s \<Longrightarrow> p \<in> kernel_regions s"
  "p \<in> kernel_device_window s \<Longrightarrow> p \<in> kernel_regions s"
  unfolding kernel_regions_def
  by auto

lemma pspace_aligned_pts_ofD:
  "\<lbrakk> pspace_aligned s; pts_of s pt_ptr \<noteq> None \<rbrakk> \<Longrightarrow> is_aligned pt_ptr pt_bits"
  by (fastforce dest: pspace_alignedD simp: in_omonad bit_simps)

lemma riscv_global_pts_aligned:
  "\<lbrakk> pt_ptr \<in> riscv_global_pts (arch_state s) level; pspace_aligned s; valid_global_arch_objs s \<rbrakk>
   \<Longrightarrow> is_aligned pt_ptr pt_bits"
  unfolding valid_global_arch_objs_def
  by (fastforce dest: pspace_aligned_pts_ofD simp: pt_at_eq)

(* FIXME MOVE *)
lemma option_Some_value_independent:
  "\<lbrakk> f x = Some v; \<And>v'. f x = Some v' \<Longrightarrow> f y = Some v' \<rbrakk> \<Longrightarrow> f y = Some v"
  by blast

(* FIXME MOVE, might break proofs elsewhere *)
lemma if_Some_Some[simp]:
  "((if P then Some v else None) = Some v) = P"
  by simp

lemma set_pt_valid_global_vspace_mappings:
  "\<lbrace>\<lambda>s. valid_global_vspace_mappings s \<and> valid_global_tables s \<and> p \<notin> global_refs s
        \<and> pspace_aligned s \<and> valid_global_arch_objs s \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wpsimp wp: set_object_wp)
  unfolding valid_global_vspace_mappings_def Let_def
  apply (safe; clarsimp; drule (1) bspec; thin_tac "Ball _ _")
   (* we don't care about whether we're in kernel window or kernel_elf_window *)
   apply (all \<open>drule kernel_regionsI, erule option_Some_value_independent\<close>)
   apply (distinct_subgoals)
   apply (subst pt_lookup_target_translate_address_upd_eq; assumption?)
   apply (clarsimp simp: translate_address_def in_omonad)
   apply (rename_tac level p')
   apply (subst pt_lookup_target_pt_upd_eq)
        apply clarsimp
        apply (frule valid_global_tablesD)
         apply assumption
        apply (clarsimp simp: kernel_regions_def)
        apply (clarsimp simp: global_refs_def)
        apply (fastforce dest: riscv_global_pts_aligned)
       apply fastforce
      apply fastforce
     apply fastforce
    apply (fastforce simp: global_refs_def elim!: valid_global_arch_objs_pt_at)
   apply assumption
  done

lemma set_pt_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_pspace_respects_device_region get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_caps_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done

lemma set_pt_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_pt p pt \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_cap_refs_respects_device_region get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  done


lemma set_pt_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_pt_def)
  apply (wp set_object_valid_ioc_no_caps get_object_wp)
  by (clarsimp simp: a_type_simps obj_at_def is_tcb is_cap_table
              split: kernel_object.splits arch_kernel_obj.splits)



lemma valid_machine_stateE:
  assumes vm: "valid_machine_state s"
  assumes e: "\<lbrakk>in_user_frame p s
    \<or> underlying_memory (machine_state s) p = 0 \<rbrakk> \<Longrightarrow> E "
  shows E
  using vm
  apply (clarsimp simp: valid_machine_state_def)
  apply (drule_tac x = p in spec)
  apply (rule e)
  apply auto
  done

lemma in_user_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj; in_user_frame q s\<rbrakk>
    \<Longrightarrow> in_user_frame q (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_user_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma in_device_frame_same_type_upd:
  "\<lbrakk>typ_at type p s; type = a_type obj ; in_device_frame q s\<rbrakk>
    \<Longrightarrow> in_device_frame q (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: in_device_frame_def obj_at_def)
  apply (rule_tac x=sz in exI)
  apply (auto simp: a_type_simps)
  done

lemma store_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma store_word_offs_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> store_word_offs a x w \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)


lemma as_user_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma as_user_in_device_frame[wp]:
  "\<lbrace>\<lambda>s. in_device_frame p s\<rbrace> as_user t m \<lbrace>\<lambda>_ s. in_device_frame p s\<rbrace>"
  unfolding in_device_frame_def
  by (wp hoare_vcg_ex_lift)

crunch obj_at[wp]: load_word_offs "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_in_user_frame[wp]:
  "\<lbrace>\<lambda>s. in_user_frame p s\<rbrace> load_word_offs a x \<lbrace>\<lambda>_ s. in_user_frame p s\<rbrace>"
  unfolding in_user_frame_def
  by (wp hoare_vcg_ex_lift)

lemma valid_machine_state_heap_updI:
assumes vm : "valid_machine_state s"
assumes tyat : "typ_at type p s"
shows
  " a_type obj = type \<Longrightarrow> valid_machine_state (s\<lparr>kheap := kheap s(p \<mapsto> obj)\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def)
  subgoal for p
   apply (rule valid_machine_stateE[OF vm,where p = p])
   apply (elim disjE,simp_all)
   apply (drule(1) in_user_frame_same_type_upd[OF tyat])
    apply simp+
   done
  done

lemma set_pt_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
   apply (fastforce simp: obj_at_def a_type_def
                   split: kernel_object.splits arch_kernel_obj.splits)+
  done

crunch valid_irq_states[wp]: set_pt "valid_irq_states"
  (wp: crunch_wps)


(* FIXME: move to ArchInvariants_A *)
lemma invs_valid_asid_table [elim!]:
  "invs s \<Longrightarrow> valid_asid_table s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)


(* FIXME: move to ArchInvariants_A *)
lemma valid_asid_table_ran:
  "valid_asid_table s \<Longrightarrow> \<forall>p\<in>ran (asid_table s). asid_pool_at p s"
  unfolding invs_def valid_state_def valid_arch_state_def valid_asid_table_def
  sorry (* FIXME RISCV *)


lemma vs_lookup_pages_pt_eq:
  "\<lbrakk>valid_vspace_objs s;
    \<forall>p\<in>ran (asid_table s). asid_pool_at p s;
    pt_at p s\<rbrakk>
   \<Longrightarrow> (vs_lookup_target level asid vref s = Some (level, p))
       = (vs_lookup_table level asid vref s = Some (level, p))"
  sorry (* FIXME RISCV: something along these lines, possibly level+1 on one side;
                        check if needed before proving it *)

lemmas invs_ran_asid_table = invs_valid_asid_table[THEN valid_asid_table_ran]


lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_iflive)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def live_def hyp_live_def)
  done


lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done


lemma set_asid_pool_zombies_state_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def split: option.splits)
  done

lemma set_asid_pool_zombies_state_hyp_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_asid_pool_def wp: get_object_wp set_object_wp)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_hyp_refs_of_def split: option.splits)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by wpsimp

lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def set_object_def including unfold_objects
  apply wpsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ _ y by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def set_object_def)


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_asid_pool_def)


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def)


lemma set_asid_pool_reply_caps [wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_asid_pool_reply_masters [wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


crunch global_ref [wp]: set_asid_pool "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)


crunch idle [wp]: set_asid_pool "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


crunch irq [wp]: set_asid_pool "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch valid_irq_states[wp]: set_asid_pool "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)


crunch interrupt_states[wp]: set_asid_pool "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_asid_pool_vspace_objs_unmap':
  "\<lbrace>valid_vspace_objs and
    (\<lambda>s. (\<exists>\<rhd> (asid_pool_level, p) s \<longrightarrow> valid_vspace_obj asid_pool_level (ASIDPool ap) s)) and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  sorry (* FIXME RISCV *)

lemma set_asid_pool_vspace_objs_unmap:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S)  \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  apply (wp set_asid_pool_vspace_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_vspace_objsD, assumption, assumption, simp add: obj_at_def in_opt_map_eq)
  apply simp
  by (auto simp: obj_at_def dest!: ran_restrictD)

lemma set_asid_pool_table_caps[wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  done

(* FIXME: Move to ArchInvariants_A *)
lemma vs_lookup_target_stateI:
  assumes 1: "vs_lookup_target bot_level asid vref s = Some (level, p)"
  assumes pts: "\<And>p pt. pts_of s p = Some pt \<Longrightarrow> \<exists>pt'. pts_of s' p = Some pt' \<and> graph_of (pte_ref o pt) \<subseteq> graph_of (pte_ref o pt')"
  assumes pools: "\<And>p ap. asid_pools_of s p = Some ap \<Longrightarrow> \<exists>ap'. asid_pools_of s' p = Some ap' \<and> graph_of ap \<subseteq> graph_of ap'"
  assumes table: "graph_of (asid_table s) \<subseteq> graph_of (asid_table s')"
  shows "vs_lookup_target bot_level asid vref s' = Some (level, p)"
  sorry (* FIXME RISCV *)
(*
  using 1 vs_lookup_pages_sub [OF ko table] by blast
*)

lemma set_asid_pool_vs_lookup_unmap':
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def)
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule allE)+
  apply (erule impE)
   apply (erule vs_lookup_target_stateI; clarsimp simp: in_opt_map_eq split: if_split_asm)
  apply fastforce
  done

lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])

lemma valid_pte_typ_at:
  "(\<And>T p. typ_at (AArch T) p s = typ_at (AArch T) p s') \<Longrightarrow>
   valid_pte level pte s = valid_pte level pte s'"
  by (case_tac pte, auto simp add: data_at_def)

lemma set_asid_pool_global_objs [wp]:
  "set_asid_pool p ap \<lbrace>valid_global_objs\<rbrace>"
  by (clarsimp simp: valid_global_objs_def) wp

crunch v_ker_map[wp]: set_asid_pool "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)

lemma set_asid_pool_vspace_objs_unmap_single:
  "\<lbrace>valid_vspace_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  using set_asid_pool_vspace_objs_unmap[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)


lemma set_asid_pool_equal_mappings[wp]:
  "\<lbrace>equal_kernel_mappings and
    (\<lambda>s. \<forall>p pt. p \<in> ran ap \<longrightarrow> pts_of s p = Some pt \<longrightarrow> has_kernel_mappings pt s)\<rbrace>
    set_asid_pool p ap
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  sorry (* FIXME RISCV *)

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def)
  sorry (* FIXME RISCV
  apply (wp set_object_global_vspace_mappings get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def) *)

lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)

lemma set_asid_pool_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_respects_device_region get_object_wp)
  including unfold_objects_asm
  by (clarsimp simp: a_type_def)


lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  including unfold_objects_asm
  by clarsimp

lemma set_asid_pool_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_respects_device_region get_object_wp)
  including unfold_objects_asm
  by clarsimp


lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_ioc_no_caps get_object_inv)
  including unfold_objects
  by (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table)


lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)+
  done


lemma set_asid_pool_valid_asid_pool_caps[wp]:
  "set_asid_pool p ap \<lbrace>valid_asid_pool_caps\<rbrace>"
  unfolding valid_asid_pool_caps_def
  sorry (* FIXME RISCV *)

lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and (\<lambda>s. \<exists>a. asid_table s a = Some p) \<rbrace>
       set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def valid_asid_map_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_vspace_objs_unmap  valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap)
  apply (clarsimp simp: equal_kernel_mappings_def)
  sorry


lemmas set_asid_pool_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF set_asid_pool_caps_of_state]


lemma mdb_cte_at_set_asid_pool[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>
   set_asid_pool y pool
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and (\<lambda>s. \<exists>a. asid_table s a = Some p) \<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma valid_slots_typ_at:
  assumes x: "\<And>T p. f \<lbrace>typ_at (AArch T) p\<rbrace>"
  assumes y: "\<And>P. f \<lbrace> \<lambda>s. P (vs_lookup s) \<rbrace>"
  assumes z: "\<And>P. f \<lbrace> \<lambda>s. P (user_region s) \<rbrace>"
  shows "\<lbrace>valid_slots m\<rbrace> f \<lbrace>\<lambda>rv. valid_slots m\<rbrace>"
  unfolding valid_slots_def
  apply (cases m; clarsimp)
  apply (wp hoare_vcg_ex_lift assms)
  sorry (* FIXME RISCV *)

lemma ucast_ucast_id:
  "len_of TYPE('a) < len_of TYPE('b) \<Longrightarrow> ucast (ucast (x::'a::len word)::'b::len word) = x"
  by (auto intro: ucast_up_ucast_id simp: is_up_def source_size_def target_size_def word_size)

lemma word_shift_by_n:
  "x * (2^n) = (x::'a::len word) << n"
  by (simp add: shiftl_t2n)

lemma is_aligned_addrFromPPtr_n:
  "\<lbrakk> is_aligned p n; n \<le> canonical_bit \<rbrakk> \<Longrightarrow> is_aligned (addrFromPPtr p) n"
  apply (simp add: addrFromPPtr_def)
  apply (erule aligned_sub_aligned; simp add: canonical_bit_def)
  apply (simp add: baseOffset_def pptrBase_def pAddr_base_def canonical_bit_def)
  apply (erule is_aligned_weaken[rotated])
  apply (simp add: is_aligned_def)
  done

lemma is_aligned_addrFromPPtr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (addrFromPPtr p) pageBits"
  by (simp add: is_aligned_addrFromPPtr_n pageBits_def canonical_bit_def)

lemma is_aligned_ptrFromPAddr_n:
  "\<lbrakk>is_aligned x sz; sz \<le> canonical_bit\<rbrakk>
  \<Longrightarrow> is_aligned (ptrFromPAddr x) sz"
  apply (simp add: ptrFromPAddr_def baseOffset_def pptrBase_def pAddr_base_def canonical_bit_def)
  apply (erule aligned_add_aligned)
   apply (erule is_aligned_weaken[rotated])
   apply (simp add:is_aligned_def)
  apply (rule order.refl)
  done

lemma is_aligned_ptrFromPAddr:
  "is_aligned p pageBits \<Longrightarrow> is_aligned (ptrFromPAddr p) pageBits"
  by (simp add: is_aligned_ptrFromPAddr_n pageBits_def canonical_bit_def)


lemma pool_for_asid_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
  pool_for_asid asid (arch_state_update f s) = pool_for_asid asid s"
  by (simp add: pool_for_asid_def obind_def split: option.splits)

lemma vs_lookup_table_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_table level asid vref (arch_state_update f s) = vs_lookup_table level asid vref s"
  by (simp add: vs_lookup_table_def obind_def split: option.splits)

lemma vs_lookup_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup (arch_state_update f s) = vs_lookup s"
  by (rule ext)+ simp

lemma vs_lookup_slot_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_slot level asid vref (arch_state_update f s) = vs_lookup_slot level asid vref s"
  by (simp add: vs_lookup_slot_def obind_def split: option.splits)

lemma vs_lookup_target_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_target level asid vref (arch_state_update f s) = vs_lookup_target level asid vref  s"
  by (simp add: vs_lookup_target_def obind_def split: option.splits)

lemma vs_lookup_pages_arch_update[simp]:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<Longrightarrow>
   vs_lookup_pages (arch_state_update f s) = vs_lookup_pages s"
  by (rule ext)+ simp

lemma store_pte_valid_vspace_objs[wp]:
  "\<lbrace>valid_vspace_objs and (\<lambda>s. \<forall>level. \<exists>\<rhd> (level, p && ~~mask pt_bits) s \<longrightarrow> valid_pte level pte s)\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding store_pte_def
  apply (wpsimp simp: valid_vspace_objs_def in_opt_map_eq obj_at_def)
  apply fastforce
  done

lemma unique_table_caps_ptE:
  "\<lbrakk> unique_table_caps_2 cs; cs p = Some cap; vs_cap_ref cap = None;
     cs p' = Some cap'; vs_cap_ref cap' = Some v; is_pt_cap cap;
     is_pt_cap cap'; obj_refs cap' = obj_refs cap \<rbrakk>
       \<Longrightarrow> P"
  apply (frule(6) unique_table_caps_ptD[where cs=cs])
  apply simp
  done

lemma set_pt_mappings[wp]:
  "\<lbrace>\<top>\<rbrace> set_pt p pt \<lbrace>\<lambda>_. valid_kernel_mappings\<rbrace>"
  by (simp add: valid_kernel_mappings_def) wp

lemma set_pt_has_kernel_mappings:
  "\<lbrace>\<lambda>s. p \<noteq> riscv_global_pt (arch_state s) \<and> has_kernel_mappings pt s \<rbrace>
   set_pt p pt'
   \<lbrace>\<lambda>_. has_kernel_mappings pt \<rbrace>"
  unfolding has_kernel_mappings_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift)
    apply (rule hoare_lift_Pf2[where f="\<lambda>s. riscv_global_pt (arch_state s)"])
     apply (wpsimp wp: set_pt_pts_of)+
  done

(* FIXME RISCV currently unused
   FIXME RISCV the not-global-pt requirement is a bit left field, we don't have a convenient
     way to go from vspace_for_asid to "not a global pt" *)
lemma set_pt_equal_kernel_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
        \<and> ((\<exists>asid. vspace_for_asid asid s = Some p) \<longrightarrow> has_kernel_mappings pt s)
        \<and> p \<noteq> riscv_global_pt (arch_state s) \<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  unfolding equal_kernel_mappings_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' vspace_for_asid_lift set_pt_pts_of
                 set_pt_has_kernel_mappings)

lemma store_pte_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> store_pte ptr val \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_refs_of_def obj_at_def)
  done

lemma store_pde_state_hyp_refs_of:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> store_pte ptr val \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: store_pte_def set_pt_def)
  apply (wp get_object_wp set_object_wp)
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  apply (clarsimp simp: state_hyp_refs_of_def obj_at_def)
  done

(* FIXME RISCV: might need tweaks and/or separate lemmas for map/unmap *)
lemma set_pt_invs:
  "\<lbrace>invs and (\<lambda>s. \<forall>i. wellformed_pte (pt i)) and
    (\<lambda>s. (\<exists>level. (\<exists>\<rhd> (level,p)) s \<longrightarrow> valid_vspace_obj level (PageTable pt) s) \<and>
         (\<exists>slot asid. caps_of_state s slot = Some (ArchObjectCap (PageTableCap p asid)) \<and>
                      pt = empty_pt \<or> asid \<noteq> None) \<and>
         (\<forall>level' asid vref. vs_lookup_target level' asid vref s = Some (level', p) \<longrightarrow>
            (\<forall>x p. pte_ref (pt x) = Some p \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                              obj_refs cap = {p} \<and>
                              vs_cap_ref cap = Some (asid, vref_for_level vref level')))) \<and>
         ((\<exists>asid. vspace_for_asid asid s = Some p) \<longrightarrow> has_kernel_mappings pt s) \<and>
         p \<notin> global_refs s)\<rbrace>
   set_pt p pt
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_state_def)
  apply (wpsimp wp: set_pt_valid_objs set_pt_iflive set_pt_zombies
                    set_pt_zombies_state_refs set_pt_zombies_state_hyp_refs set_pt_valid_mdb
                    set_pt_valid_idle set_pt_ifunsafe set_pt_reply_caps
                    set_pt_valid_global set_pt_cur
                    set_pt_reply_masters valid_irq_node_typ
                    valid_irq_handlers_lift
                    set_pt_valid_global_vspace_mappings
                    set_pt_equal_kernel_mappings)
  sorry (* FIXME RISCV
  apply (clarsimp dest!: valid_objs_caps)
  apply (rule conjI[rotated])
  apply (subgoal_tac "p \<notin> global_refs s", simp add: global_refs_def)
  apply (frule (1) valid_global_refsD2)
  apply (clarsimp simp add: cap_range_def is_pt_cap_def)
  apply (thin_tac "ALL x. P x" for P)+
  apply (clarsimp simp: valid_arch_caps_def unique_table_caps_def)
  apply (drule_tac x=aa in spec, drule_tac x=ba in spec)
  apply (drule_tac x=a in spec, drule_tac x=b in spec)
  apply (clarsimp simp: is_pt_cap_def cap_asid_def)
  done *)

lemma store_pte_invs:
  "\<lbrace>invs and (\<lambda>s. (\<forall>level. \<exists>\<rhd>(level, table_base p) s \<longrightarrow> valid_pte level pte s)) and (* potential off-by-one in level *)
    K (wellformed_pte pte) and
    (\<lambda>s. \<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref)) \<and>
                     (pte = InvalidPTE \<or> ref \<noteq> None)) and
    (\<lambda>s. \<forall>level asid vref. vs_lookup_target level asid vref s = Some (level, p) \<longrightarrow>
            (\<forall>q. pte_ref pte = Some q \<longrightarrow>
                    (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
                         obj_refs cap = {q} \<and>
                         vs_cap_ref cap = Some (asid, vref_for_level vref level)))) and (* potential off-by-one in level *)
    (\<lambda>s. (\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) and
    (\<lambda>s. table_base p \<notin> global_refs s) \<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: store_pte_def)
  apply (wp dmo_invs set_pt_invs)
  apply clarsimp
  apply (intro conjI)
     apply (drule invs_valid_objs)
     apply (fastforce simp: valid_objs_def dom_def obj_at_def valid_obj_def arch_valid_obj_def)
  sorry (* FIXME RISCV
    apply clarsimp
    apply (drule (1) valid_vspace_objsD, fastforce)
    apply simp
   apply (thin_tac "All _")
   apply (rule exI)+
   apply (rule conjI, assumption)
   subgoal premises prems for \<dots> asid
   proof (cases asid)
    case (Some a) from this show ?thesis
     by fastforce
    next
    case None from this prems show ?thesis
     apply clarsimp
     apply (rule ext)
     apply clarsimp
     apply (frule invs_pd_caps)
     apply (clarsimp simp add: valid_table_caps_def simp del: HOL.imp_disjL)
     apply (spec "p && ~~ mask pt_bits")
     apply (drule spec)+
     apply (erule impE, assumption)
     by (simp add: is_pt_cap_def cap_asid_def empty_table_def obj_at_def)
  qed
  apply (clarsimp simp: obj_at_def)
  apply (intro impI conjI allI)
   apply (drule (2) vs_lookup_pages_pt_eq[OF invs_vspace_objs invs_ran_asid_table,
                                          THEN iffD1, rotated -1])
    apply (clarsimp simp: obj_at_def a_type_simps)
   apply (drule spec, erule impE, assumption)+
   apply (erule exEI)+
   apply clarsimp
   apply (rule sym)
   apply (rule ucast_ucast_len)
   apply (rule shiftr_less_t2n)
   using and_mask_less'[of 10 p]
   apply (simp add: pt_bits_def pageBits_def)
  subgoal for \<dots> pa
   apply (thin_tac "All _", thin_tac "_ \<longrightarrow> _", thin_tac "_ \<or> _")
   apply (frule invs_valid_vs_lookup)
   apply (simp add: valid_vs_lookup_def)
   apply (spec pa)
   apply (drule spec, erule impE)
    apply (erule vs_lookup_pages_step)
    by (fastforce simp: vs_lookup_pages1_def obj_at_def
                          vs_refs_pages_def graph_of_def image_def) simp
  done *)


lemma store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<exists>slot ref. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) ref))) and
    (\<lambda>s. (\<exists>asid. vspace_for_asid asid s = Some (table_base p)) \<longrightarrow> table_index p \<notin> kernel_mapping_slots) and
    (\<lambda>s. table_base p \<notin> global_refs s) and K (pte = InvalidPTE)\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: store_pte_invs simp: wellformed_pte_def)


lemma pspace_respects_device_region_dmo:
  assumes valid_f: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>pspace_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
                        get_def return_def)
  apply (drule_tac P2 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

lemma cap_refs_respects_device_region_dmo:
  assumes valid_f: "\<And>P. f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  shows "do_machine_op f \<lbrace>cap_refs_respects_device_region\<rbrace>"
  apply (clarsimp simp: do_machine_op_def gets_def select_f_def simpler_modify_def bind_def valid_def
                        get_def return_def)
  apply (drule_tac P2 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_f])
  apply auto
  done

lemma machine_op_lift_device_state[wp]:
  "machine_op_lift f \<lbrace>\<lambda>ms. P (device_state ms)\<rbrace>"
  by (clarsimp simp: machine_op_lift_def NonDetMonad.valid_def bind_def
                     machine_rest_lift_def gets_def simpler_modify_def get_def return_def
                     select_def ignore_failure_def select_f_def
              split: if_splits)

crunch device_state_inv[wp]: sfence "\<lambda>ms. P (device_state ms)"
crunch device_state_inv[wp]: hwASIDFlush "\<lambda>ms. P (device_state ms)"
crunch device_state_inv[wp]: setVSpaceRoot "\<lambda>ms. P (device_state ms)"

lemma as_user_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> as_user t f \<lbrace>\<lambda>x. P\<rbrace>"
proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have Q: "\<And>s ps. ps (kheap s) = kheap s \<Longrightarrow> kheap_update ps s = s"
    by simp
  show ?thesis
    apply (simp add: as_user_def gets_the_def assert_opt_def set_object_def split_def)
    apply wp
    apply (clarsimp dest!: P)
    apply (subst Q)
     prefer 2
     apply assumption
    apply (rule ext)
    apply (simp add: get_tcb_def)
    apply (case_tac "kheap s t"; simp)
    apply (case_tac a; simp)
    apply (clarsimp simp: arch_tcb_context_set_def arch_tcb_context_get_def)
    done
qed

lemma user_getreg_inv[wp]:
  "\<lbrace>P\<rbrace> as_user t (getRegister r) \<lbrace>\<lambda>x. P\<rbrace>"
  apply (rule as_user_inv)
  apply (simp add: getRegister_def)
  done

end

end
