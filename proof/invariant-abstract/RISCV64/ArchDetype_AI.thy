(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchDetype_AI
imports "../Detype_AI"
begin

context Arch begin global_naming RISCV64

(* FIXME RISCV: move up *)
lemma invs_valid_uses[elim!]:
  "invs s \<Longrightarrow> valid_uses s"
  by (simp add: invs_def valid_state_def valid_arch_state_def)

(* FIXME RISCV: move up *)
lemma asid_high_bits_of_and_mask[simp]:
  "asid_high_bits_of (asid && ~~ mask asid_low_bits || UCAST(10 \<rightarrow> 64) asid_low) =
   asid_high_bits_of asid"
  apply (simp add: asid_high_bits_of_def asid_low_bits_def)
  apply word_bitwise
  apply (simp add: word_size)
  done

(* FIXME RISCV: move up *)
lemma asid_low_bits_of_and_mask[simp]:
  "asid_low_bits_of (asid && ~~ mask asid_low_bits || ucast (asid_low::asid_low_index)) = asid_low"
  apply (simp add: asid_low_bits_of_def asid_low_bits_def)
  apply word_bitwise
  apply (simp add: word_size)
  done

(* FIXME RISCV: move up *)
lemma pool_for_asid_and_mask[simp]:
  "pool_for_asid (asid && ~~ mask asid_low_bits || ucast (asid_low::asid_low_index)) s =
   pool_for_asid asid s"
  by (simp add: pool_for_asid_def)

(* FIXME RISCV: move up *)
lemma vs_lookup_table_ap_step:
  "\<lbrakk> vs_lookup_table asid_pool_level asid vref s = Some (asid_pool_level, p); vref \<in> user_region s;
     asid_pools_of s p = Some ap; pt \<in> ran ap \<rbrakk> \<Longrightarrow>
   \<exists>asid'. vs_lookup_target asid_pool_level asid' vref s = Some (asid_pool_level, pt)"
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def in_omonad ran_def)
  apply (rename_tac asid_low)
  apply (rule_tac x="asid && ~~mask asid_low_bits || ucast asid_low" in exI)
  apply (fastforce simp: vs_lookup_table_def vspace_for_pool_def in_omonad)
  done

(* FIXME RISCV: move up *)
locale_abbrev vref_for_index :: "pt_index \<Rightarrow> vm_level \<Rightarrow> vspace_ref" where
  "vref_for_index idx level \<equiv> ucast (idx::pt_index) << pt_bits_left level"

(* FIXME RISCV: move up *)
locale_abbrev vref_for_level_idx :: "vspace_ref \<Rightarrow> pt_index \<Rightarrow> vm_level \<Rightarrow> vspace_ref" where
  "vref_for_level_idx vref idx level \<equiv> vref_for_level vref (level+1) || vref_for_index idx level"

(* FIXME RISCV: move up *)
lemma table_index_pt_slot_offset:
  "\<lbrakk> is_aligned p pt_bits; level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   table_index (pt_slot_offset level p (vref_for_level_idx vref idx level)) = idx"
  using pt_bits_left_bound[of "level"]
  using pt_bits_left_bound[of "level+1"]
  apply (simp add: pt_slot_offset_def pt_index_def vref_for_level_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr bit_simps neg_mask_bang)
   apply (clarsimp simp: pt_bits_left_def bit_simps is_aligned_nth)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr bit_simps neg_mask_bang)
  apply (clarsimp simp: bit_simps is_aligned_nth canonical_bit_def pt_bits_left_def)
  done

(* FIXME RISCV: move up *)
lemma vs_lookup_vref_for_level_eq1:
  "vref_for_level vref' (bot_level+1) = vref_for_level vref (bot_level+1) \<Longrightarrow>
   vs_lookup_table bot_level asid vref' = vs_lookup_table bot_level asid vref"
  apply (rule ext)
  apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits)
  apply (rule conjI; clarsimp)+
  apply (erule pt_walk_vref_for_level_eq[THEN fun_cong])
  apply simp
  done

(* FIXME RISCV: move up *)
lemma vref_for_level_idx[simp]:
  "level \<le> max_pt_level \<Longrightarrow>
   vref_for_level (vref_for_level_idx vref idx level) (level + 1) =
   vref_for_level vref (level + 1)"
  apply (simp add: vref_for_level_def pt_bits_left_def)
  apply (rule word_eqI)
  apply (clarsimp simp: word_eqI_solve_simps bit_simps)
  apply (rule iffI; clarsimp)
  apply (drule test_bit_size)
  apply (clarsimp simp: word_size)
  apply (simp flip: bit0.size_less_eq)
  done

(* FIXME RISCV: move up *)
lemma vref_for_level_nth[simp]:
  "vref_for_level vref level !! n = (vref !! n \<and> pt_bits_left level \<le> n \<and> n < size vref)"
  by (simp add: vref_for_level_def word_eqI_solve_simps)

(* FIXME RISCV: move up *)
lemma pt_bits_left_max:
  "pt_bits_left max_pt_level = canonical_bit - (LENGTH(pt_index_len)-1)"
  by (simp add: pt_bits_left_def level_defs bit_simps canonical_bit_def)

(* FIXME RISCV: move up *)
lemma kernel_mapping_slots_top_bit:
  "(idx \<in> kernel_mapping_slots) = (idx !! (LENGTH(pt_index_len)-1))"
  apply (simp add: kernel_mapping_slots_def pptr_base_mask pt_bits_left_max)
  apply word_bitwise
  apply (simp add: canonical_bit_def word_size rev_bl_order_simps)
  done

(* FIXME RISCV: move up *)
lemma vref_for_level_idx_canonical_user:
  "\<lbrakk> vref \<le> canonical_user; level \<le> max_pt_level; level = max_pt_level \<longrightarrow> idx \<notin> kernel_mapping_slots \<rbrakk> \<Longrightarrow>
   vref_for_level_idx vref idx level \<le> canonical_user"
  apply (simp add: canonical_user_def le_mask_high_bits)
  apply (clarsimp simp: word_size)
  apply (cases "level < max_pt_level")
   apply (clarsimp simp: word_eqI_solve_simps canonical_bit_def)
   apply (simp add: pt_bits_left_def bit_simps)
   apply (frule test_bit_size)
   apply (simp add: word_size level_defs flip: bit0.size_less)
  apply (simp add: not_less)
  apply (clarsimp simp: word_eqI_solve_simps canonical_bit_def kernel_mapping_slots_top_bit)
  apply (simp add: pt_bits_left_def bit_simps level_defs)
  apply (frule test_bit_size)
  apply (simp add: word_size)
  apply (subgoal_tac "i \<noteq> canonical_bit"; fastforce simp: canonical_bit_def)
  done

(* FIXME RISCV: move up *)
lemma vs_lookup_table_pt_step:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); vref \<in> user_region s;
     pts_of s p = Some pt; is_aligned p pt_bits; level \<le> max_pt_level; pte_ref (pt idx) = Some x;
     level = max_pt_level \<longrightarrow> idx \<notin> kernel_mapping_slots;
     valid_uses s \<rbrakk> \<Longrightarrow>
   \<exists>vref'. vs_lookup_target level asid vref' s = Some (level, x) \<and>
           vref' \<in> user_region s"
  apply (rule_tac x="vref_for_level vref (level+1) ||
                     (ucast (idx::pt_index) << pt_bits_left level)" in exI)
  apply (simp add: vs_lookup_target_def vs_lookup_slot_def in_omonad)
  apply (rule conjI)
   apply (rule_tac x="pt_slot_offset level p (vref_for_level_idx vref idx level)" in exI)
   apply (rule conjI, clarsimp)
   apply (rule conjI)
    apply (rule_tac x=level in exI)
    apply (rule_tac x=p in exI)
    apply clarsimp
    apply (rule conjI, clarsimp)
    apply (subst vs_lookup_vref_for_level_eq1)
     prefer 2
     apply assumption
    apply simp
   apply (simp add: pte_of_def in_omonad is_aligned_pt_slot_offset_pte table_index_pt_slot_offset)
  apply (simp add: valid_uses_user_region_eq vref_for_level_idx_canonical_user)
  done

named_theorems Detype_AI_asms

lemma valid_globals_irq_node[Detype_AI_asms]:
    "\<lbrakk> valid_global_refs s; cte_wp_at ((=) cap) ptr s \<rbrakk>
          \<Longrightarrow> interrupt_irq_node s irq \<notin> cap_range cap"
    apply (erule(1) valid_global_refsD)
    apply (simp add: global_refs_def)
    done

lemma caps_of_state_ko[Detype_AI_asms]:
  "valid_cap cap s
   \<Longrightarrow> is_untyped_cap cap \<or>
       cap_range cap = {} \<or>
       (\<forall>ptr \<in> cap_range cap. \<exists>ko. kheap s ptr = Some ko)"
  apply (case_tac cap)
    apply (clarsimp simp: cap_range_def valid_cap_def obj_at_def is_cap_simps
                   split: option.splits)+
  apply (rename_tac arch_cap ptr)
  apply (case_tac arch_cap)
    apply (fastforce simp: cap_range_def obj_at_def is_cap_simps
                    split: option.splits if_splits)+
  done

lemma mapM_x_storeWord[Detype_AI_asms]:
(* FIXME: taken from Retype_C.thy and adapted wrt. the missing intvl syntax. *)
  assumes al: "is_aligned ptr word_size_bits"
  shows "mapM_x (\<lambda>x. storeWord (ptr + of_nat x * word_size) 0) [0..<n]
  = modify (underlying_memory_update
             (\<lambda>m x. if \<exists>k. x = ptr + of_nat k \<and> k < n * word_size then 0 else m x))"
proof (induct n)
  case 0
  thus ?case
    apply (rule ext)
    apply (simp add: mapM_x_mapM mapM_def sequence_def
                     modify_def get_def put_def bind_def return_def)
    done
next
  case (Suc n')

  have b: "\<And>i. word_rsplit (0 :: machine_word) ! (7 - i) = (0 :: 8 word)"
    apply (simp add: word_rsplit_0)
    apply (case_tac i; simp; rename_tac i)+
    done

  have k: "\<And>k. (k < word_size + n' * word_size)
                  = (k < n' * word_size \<or> k = n' * word_size
                        \<or> (\<exists>i \<in> {1,2,3,4,5,6,7}. k = n' * word_size + i))"
    by (auto simp: word_size_def)

  have x: "\<And>x. (\<exists>k. x = ptr + of_nat k \<and> k < word_size + n' * word_size)
                  = ((\<exists>k. x = ptr + of_nat k \<and> k < n' * word_size)
                       \<or> (\<exists>i \<in> {0,1,2,3,4,5,6,7}. x = ptr + of_nat n' * word_size + i))"
    unfolding k by (simp add: word_size_def conj_disj_distribL ex_disj_distrib field_simps)

  from al have "is_aligned (ptr + of_nat n' * word_size) word_size_bits"
    apply (rule aligned_add_aligned)
    apply (rule is_aligned_mult_triv2 [of _ word_size_bits, simplified word_size_size_bits_word])
    apply (rule order_refl)
    done

  thus ?case
    apply (simp add: mapM_x_append bind_assoc Suc.hyps mapM_x_singleton)
    apply (simp add: storeWord_def b assert_def is_aligned_mask modify_modify
                     comp_def word_size_bits_def)
    apply (rule arg_cong[where f=modify])
    apply (rule arg_cong[where f=underlying_memory_update])
    apply (rule ext, rule ext, rule sym)
    apply (simp add: x upto0_7_def)
    done
qed

lemma empty_fail_freeMemory [Detype_AI_asms]: "empty_fail (freeMemory ptr bits)"
  by (simp add: freeMemory_def mapM_x_mapM ef_storeWord)


lemma region_in_kernel_window_detype[simp]:
  "region_in_kernel_window S (detype S' s)
      = region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def detype_def)


lemma region_in_kernel_window_machine_state_update[simp]:
  "region_in_kernel_window S (machine_state_update f s) =
   region_in_kernel_window S s"
  by (simp add: region_in_kernel_window_def)


lemma region_in_kernel_window_delete_objects[wp]:
  "\<lbrace>region_in_kernel_window S\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. region_in_kernel_window S\<rbrace>"
  by (wp | simp add: delete_objects_def do_machine_op_def split_def)+

lemma state_hyp_refs_of_detype:
  "state_hyp_refs_of (detype S s) = (\<lambda>x. if x \<in> S then {} else state_hyp_refs_of s x)"
  by (rule ext, simp add: state_hyp_refs_of_def detype_def)

lemma valid_ioports_detype[Detype_AI_asms]:
  "valid_ioports s \<Longrightarrow> valid_ioports (detype (untyped_range cap) s)"
  by simp

end

interpretation Detype_AI?: Detype_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact Detype_AI_asms)?)
  qed

context detype_locale_arch begin

named_theorems detype_invs_proofs

lemma state_hyp_refs: "state_hyp_refs_of (detype (untyped_range cap) s) = state_hyp_refs_of s"
  apply (rule ext, clarsimp simp add: state_hyp_refs_of_detype)
  apply (rule sym, rule equals0I, drule state_hyp_refs_of_elemD)
  apply (drule live_okE, rule hyp_refs_of_live, clarsimp)
  apply simp
  done

lemma hyp_refsym : "sym_refs (state_hyp_refs_of s)"
  using invs by (simp add: invs_def valid_state_def valid_pspace_def)

lemma hyp_refs_of: "\<And>obj p. \<lbrakk> ko_at obj p s \<rbrakk> \<Longrightarrow> hyp_refs_of obj \<subseteq> (UNIV - untyped_range cap \<times> UNIV)"
  by (fastforce intro: hyp_refs_of_live dest!: hyp_sym_refs_ko_atD[OF _ hyp_refsym] live_okE)

lemma arch_valid_obj[detype_invs_proofs]:
    "\<And>p ao. \<lbrakk>ko_at (ArchObj ao) p s; arch_valid_obj ao s\<rbrakk>
       \<Longrightarrow> arch_valid_obj ao (detype (untyped_range cap) s)"
  by simp

lemma sym_hyp_refs_detype[detype_invs_proofs]:
  "sym_refs (state_hyp_refs_of (detype (untyped_range cap) s))"
  using hyp_refsym by (simp add: state_hyp_refs)

lemma valid_cap[detype_invs_proofs]:
    "\<And>cap'. \<lbrakk> s \<turnstile> cap'; obj_reply_refs cap' \<subseteq> (UNIV - untyped_range cap) \<rbrakk>
      \<Longrightarrow> detype (untyped_range cap) s \<turnstile> cap'"
  by (auto simp: valid_cap_def valid_untyped_def obj_reply_refs_def valid_arch_cap_ref_def
          split: cap.split_asm option.splits if_splits
                 arch_cap.split_asm bool.split_asm )

lemma glob_det[detype_invs_proofs]: "\<And>r. global_refs (detype r s) = global_refs s"
    by (simp add: global_refs_def detype_def)

lemma valid_idle_detype[detype_invs_proofs]: "valid_idle (detype (untyped_range cap) s)"
    proof -
    have "valid_idle s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis using valid_global_refsD [OF globals cap]
    by (fastforce simp add: valid_idle_def state_refs idle cap_range_def
                            global_refs_def)
    qed

lemma valid_vs_lookup: "valid_vs_lookup s"
    using valid_arch_caps by (simp add: valid_arch_caps_def)

lemma hyp_live_strg:
  "hyp_live ko \<Longrightarrow> live ko"
  by (cases ko; simp add: live_def hyp_live_def)

lemma obj_at_hyp_live_strg:
  "obj_at hyp_live p s \<Longrightarrow> obj_at live p s"
  by (erule obj_at_weakenE, rule hyp_live_strg)

lemma tcb_arch_detype[detype_invs_proofs]:
  "\<lbrakk>ko_at (TCB t) p s; valid_arch_tcb (tcb_arch t) s\<rbrakk>
      \<Longrightarrow> valid_arch_tcb (tcb_arch t) (detype (untyped_range cap) s)"
  apply (clarsimp simp: valid_arch_tcb_def)
  done

declare arch_state_det[simp]

lemma aobjs_of_detype[simp]:
  "(aobjs_of (detype S s) p = Some aobj) = (p \<notin> S \<and> aobjs_of s p = Some aobj)"
  by (simp add: in_omonad detype_def)

lemma pts_of_detype[simp]:
  "(pts_of (detype S s) p = Some pt) = (p \<notin> S \<and> pts_of s p = Some pt)"
  by (simp add: in_omonad detype_def)

lemma ptes_of_detype_Some[simp]:
  "(ptes_of (detype S s) p = Some pte) = (table_base p \<notin> S \<and> ptes_of s p = Some pte)"
  by (simp add: in_omonad ptes_of_def detype_def)

lemma asid_pools_of_detype:
  "asid_pools_of (detype S s) = (\<lambda>p. if p\<in>S then None else asid_pools_of s p)"
  by (rule ext) (simp add: detype_def opt_map_def)

lemma asid_pools_of_detype_Some[simp]:
  "(asid_pools_of (detype S s) p = Some ap) = (p \<notin> S \<and> asid_pools_of s p = Some ap)"
  by (simp add: in_omonad detype_def)

lemma pool_for_asid_detype_Some[simp]:
  "(pool_for_asid asid (detype S s) = Some p) = (pool_for_asid asid s = Some p)"
  by (simp add: pool_for_asid_def)

lemma vspace_for_pool_detype_Some[simp]:
  "(vspace_for_pool ap asid (\<lambda>p. if p \<in> S then None else pools p) = Some p) =
   (ap \<notin> S \<and> vspace_for_pool ap asid pools = Some p)"
  by (simp add: vspace_for_pool_def obind_def split: option.splits)

lemma vspace_for_asid_detype_Some[simp]:
  "(vspace_for_asid asid (detype S s) = Some p) =
   ((\<exists>ap. pool_for_asid asid s = Some ap \<and> ap \<notin> S) \<and> vspace_for_asid asid s = Some p)"
  apply (simp add: vspace_for_asid_def obind_def asid_pools_of_detype split: option.splits)
  apply (auto simp: pool_for_asid_def)
  done

lemma pt_walk_detype:
  "pt_walk level bot_level pt_ptr vref (ptes_of (detype S s)) = Some (bot_level, p) \<Longrightarrow>
   pt_walk level bot_level pt_ptr vref (ptes_of s) = Some (bot_level, p)"
  apply (induct level arbitrary: pt_ptr)
   apply (simp add: pt_walk.simps)
  apply (subst pt_walk.simps)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (drule meta_spec, drule (1) meta_mp)
  apply fastforce
  done

lemma vs_lookup_table:
  "vs_lookup_table level asid vref (detype (untyped_range cap) s) = Some (level, p) \<Longrightarrow>
   vs_lookup_table level asid vref s = Some (level, p)"
  by (fastforce simp: vs_lookup_table_def in_omonad asid_pools_of_detype pt_walk_detype
               split: if_split_asm)

lemma vs_lookup_slot:
  "(vs_lookup_slot level asid vref (detype (untyped_range cap) s) = Some (level, p)) ==>
   (vs_lookup_slot level asid vref s = Some (level, p))"
  by (fastforce simp: vs_lookup_slot_def in_omonad asid_pools_of_detype
                split: if_split_asm
                dest!: vs_lookup_table)

lemma vs_lookup_target:
  "(vs_lookup_target level asid vref (detype (untyped_range cap) s) = Some (level, p)) ==>
   (vs_lookup_target level asid vref s = Some (level, p))"
  by (fastforce simp: vs_lookup_target_def in_omonad asid_pools_of_detype
                split: if_split_asm
                dest!: vs_lookup_slot)

lemma vs_lookup_target_preserved:
  "\<lbrakk> x \<in> untyped_range cap; vs_lookup_target level asid vref s = Some (level', x);
     vref \<in> user_region s \<rbrakk> \<Longrightarrow> False"
  apply (drule (1) valid_vs_lookupD[OF _ _ valid_vs_lookup])
  apply (fastforce intro: no_obj_refs)
  done

lemma valid_asid_table:
  "valid_asid_table (detype (untyped_range cap) s)"
  using valid_arch_state
  apply (clarsimp simp: valid_asid_table_def valid_arch_state_def)
  apply (drule (1) subsetD)
  apply (clarsimp simp: ran_def)
  apply (subgoal_tac "valid_asid_pool_caps s")
   prefer 2
   using invs
   apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (simp add: valid_asid_pool_caps_def)
  apply (erule allE, erule allE, erule (1) impE)
  apply clarsimp
  apply (drule no_obj_refs; simp)
  done

lemma riscv_global_pts_global_ref:
  "pt \<in> riscv_global_pts (arch_state s) level \<Longrightarrow> pt \<in> global_refs s"
  by (auto simp: global_refs_def)

lemma valid_global_arch_objs:
  "valid_global_arch_objs (detype (untyped_range cap) s)"
  using valid_arch_state
  by (fastforce dest!: riscv_global_pts_global_ref valid_global_refsD[OF globals cap]
                simp: cap_range_def valid_global_arch_objs_def valid_arch_state_def)

lemma valid_global_tables:
  "valid_global_tables (detype (untyped_range cap) s)"
  using valid_arch_state
  by (fastforce dest: pt_walk_level pt_walk_detype
                simp: valid_global_tables_def valid_arch_state_def)

lemma valid_arch_state_detype[detype_invs_proofs]:
  "valid_arch_state (detype (untyped_range cap) s)"
  using valid_vs_lookup valid_arch_state ut_mdb valid_global_refsD [OF globals cap] cap
  unfolding valid_arch_state_def pred_conj_def
  by (simp only: valid_asid_table valid_global_arch_objs valid_global_tables) simp

lemma vs_lookup_asid_pool_level:
  assumes lookup: "vs_lookup_table level asid vref s = Some (level, p)" "vref \<in> user_region s"
  assumes ap: "asid_pools_of s p = Some ap"
  shows "level = asid_pool_level"
proof (rule ccontr)
  have "valid_vspace_objs s" using invs by fastforce
  moreover
  note lookup
  moreover
  assume "level \<noteq> asid_pool_level"
  then have "level \<le> max_pt_level" by simp
  moreover
  have "valid_uses s" "valid_asid_table s" "pspace_aligned s"
    using invs by (auto simp: invs_def valid_state_def valid_arch_state_def)
  ultimately
  have "\<exists>pt. pts_of s p = Some pt \<and> valid_vspace_obj level (PageTable pt) s"
    by (rule valid_vspace_objs_strongD)
  with ap
  show False by (clarsimp simp: in_omonad)
qed

lemma vs_lookup_pt_level:
  assumes lookup: "vs_lookup_table level asid vref s = Some (level, p)" "vref \<in> user_region s"
  assumes pt: "pts_of s p = Some pt"
  shows "level \<le> max_pt_level"
proof (rule ccontr)
  assume "\<not>level \<le> max_pt_level"
  then
  have "level = asid_pool_level" by (simp add: not_le)
  with lookup
  have "pool_for_asid asid s = Some p" by (auto simp: vs_lookup_table_def)
  moreover
  have "valid_asid_table s" using invs by (fastforce)
  ultimately
  have "asid_pools_of s p \<noteq> None" by (fastforce simp: pool_for_asid_def valid_asid_table_def)
  with pt
  show False by (simp add: in_omonad)
qed

lemma data_at_detype[simp]:
  "data_at sz p (detype S s) = (p \<notin> S \<and> data_at sz p s)"
  by (auto simp: data_at_def)

lemma valid_vspace_obj:
  "\<lbrakk> valid_vspace_obj level ao s; aobjs_of s p = Some ao; \<exists>\<rhd>(level,p) s \<rbrakk> \<Longrightarrow>
     valid_vspace_obj level ao (detype (untyped_range cap) s)"
  using invs
  apply (cases ao; clarsimp split del: if_split)
   apply (frule (1) vs_lookup_asid_pool_level, simp add: in_omonad)
   apply simp
   apply (drule (1) vs_lookup_table_ap_step, simp add: in_omonad, assumption)
   apply clarsimp
   apply (erule (2) vs_lookup_target_preserved)
  apply (rename_tac pt idx asid vref)
  apply (case_tac "pt idx"; simp)
   apply (frule_tac idx=idx in vs_lookup_table_pt_step; simp add: in_omonad)
        apply (frule pspace_alignedD, fastforce)
        apply (simp add: bit_simps)
       apply (erule (1) vs_lookup_pt_level, simp add: in_omonad)
      apply simp
     apply fastforce
    apply fastforce
   apply (fastforce elim: vs_lookup_target_preserved)
  apply (frule_tac idx=idx in vs_lookup_table_pt_step; simp add: in_omonad)
       apply (frule pspace_alignedD, fastforce)
       apply (simp add: bit_simps)
      apply (erule (1) vs_lookup_pt_level, simp add: in_omonad)
     apply simp
    apply fastforce
   apply fastforce
  apply (fastforce elim: vs_lookup_target_preserved)
  done

lemma valid_vspace_obj_detype[detype_invs_proofs]: "valid_vspace_objs (detype (untyped_range cap) s)"
proof -
  have "valid_vspace_objs s"
    using invs by fastforce
  thus ?thesis
    unfolding valid_vspace_objs_def
    apply clarsimp
    apply (drule vs_lookup_level, drule vs_lookup_table)
    apply (fastforce intro: valid_vspace_obj)
    done
qed

lemma unique_table_caps:
  "unique_table_caps s \<Longrightarrow> unique_table_caps (detype (untyped_range cap) s)"
  by (simp add: unique_table_caps_def)

end


sublocale detype_locale < detype_locale_gen_1
proof goal_cases
  interpret detype_locale_arch ..
  case 1 show ?case by (unfold_locales; fact detype_invs_proofs)
qed


context detype_locale_arch begin

lemma valid_vs_lookup':
  "valid_vs_lookup s \<Longrightarrow> valid_vs_lookup (detype (untyped_range cap) s)"
  apply (simp add: valid_vs_lookup_def del: split_paired_Ex)
  apply (intro allI impI)
  apply (drule vs_lookup_target_level, drule vs_lookup_target)
  apply (elim allE, (erule (1) impE)+)
  apply (elim conjE exE)
  apply (frule non_null_caps, clarsimp)
  apply fastforce
  done

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps (detype (untyped_range cap) s)"
  apply (simp add: valid_table_caps_def del: imp_disjL)
  apply (elim allEI | rule impI)+
  apply (fastforce dest: no_obj_refs)
  done

lemma unique_table_refs:
  "unique_table_refs s \<Longrightarrow> unique_table_refs (detype (untyped_range cap) s)"
  apply (simp only: unique_table_refs_def option.simps simp_thms caps_of_state_detype split: if_split)
  apply blast
  done

lemma valid_asid_pools_caps:
  "valid_asid_pool_caps s \<Longrightarrow> valid_asid_pool_caps (detype (untyped_range cap) s)"
  by (fastforce simp: valid_asid_pool_caps_def dest: non_null_caps)

lemma valid_arch_caps_detype[detype_invs_proofs]: "valid_arch_caps (detype (untyped_range cap) s)"
  using valid_arch_caps
  by (simp add: valid_arch_caps_def unique_table_caps valid_vs_lookup' unique_table_refs
                valid_table_caps valid_asid_pools_caps
           del: caps_of_state_detype arch_state_det)

lemma valid_global_objs_detype[detype_invs_proofs]:
  "valid_global_objs (detype (untyped_range cap) s)"
  using valid_global_objs valid_global_refsD [OF globals cap]
  by (simp add: valid_global_objs_def valid_vso_at_def)

lemma valid_kernel_mappings_detype[detype_invs_proofs]:
  "valid_kernel_mappings (detype (untyped_range cap) s)"
proof -
  have "valid_kernel_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis by (simp add: valid_kernel_mappings_def detype_def ball_ran_eq)
qed

lemma valid_asid_map_detype[detype_invs_proofs]: "valid_asid_map (detype (untyped_range cap) s)"
  by (simp add: valid_asid_map_def)

lemma has_kernel_mappings:
  "valid_global_arch_objs s \<Longrightarrow>
   has_kernel_mappings pt (detype (untyped_range cap) s) = has_kernel_mappings pt s"
  by (auto dest!: riscv_global_pt_in_global_refs valid_global_refsD [OF globals cap]
           simp: cap_range_def has_kernel_mappings_def )

lemma equal_kernel_mappings_detype[detype_invs_proofs]:
  "equal_kernel_mappings (detype (untyped_range cap) s)"
proof -
  have "equal_kernel_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  moreover
  have "valid_global_arch_objs s"
    using invs by (simp add: invs_def valid_state_def valid_arch_state_def)
  ultimately
  show ?thesis
    by (clarsimp simp: equal_kernel_mappings_def has_kernel_mappings)
qed

lemma valid_global_mappings_detype[detype_invs_proofs]:
  "valid_global_vspace_mappings (detype (untyped_range cap) s)"
proof -
  have "valid_global_vspace_mappings s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    using valid_global_refsD [OF globals cap]
    unfolding valid_global_vspace_mappings_def
    apply (simp add: Let_def)
    sorry (* FIXME RISCV, needs different argument now
    apply -
    apply (erule valid_global_vspace_mappings_pres, simp_all)
    apply (simp add: cap_range_def global_refs_def arch_state_det)+
    done *)
qed

lemma pspace_in_kernel_window_detype[detype_invs_proofs]:
  "pspace_in_kernel_window (detype (untyped_range cap) s)"
proof -
  have "pspace_in_kernel_window s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    by (simp add: pspace_in_kernel_window_def)
qed

lemma in_user_frame_eq:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                     Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
                     order_class.Icc_eq_Icc
    and [simp] = p2pm1_to_mask
  shows "p \<notin> untyped_range cap \<Longrightarrow> in_user_frame p
              (trans_state (\<lambda>_. detype_ext (untyped_range cap) (exst s)) s
               \<lparr>kheap := \<lambda>x. if x \<in> untyped_range cap then None else kheap s x\<rparr>)
         = in_user_frame p s"
    using cap_is_valid untyped
    apply (cases cap; simp add: in_user_frame_def valid_untyped_def valid_cap_def obj_at_def)
    apply (rule iffI; erule exEI; elim conjE exE; simp)
    subgoal for dev ptr n f sz ko
      apply (elim allE; erule (1) impE)
      apply (drule valid_pspace_aligned[OF valid_pspace])
      apply (clarsimp simp: obj_range_def)
      apply (erule impE)
       apply (erule not_emptyI[rotated])
       apply (rule mask_in_range[THEN iffD1, simplified])
        apply (simp add: is_aligned_neg_mask)
       apply (simp add: mask_lower_twice)
      apply (cut_tac mask_in_range[THEN iffD1, simplified, OF is_aligned_neg_mask[OF le_refl] refl])
      apply fastforce
      done
    done

lemma in_device_frame_eq:
  notes blah[simp del] =  atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
          order_class.Icc_eq_Icc
     and  p2pm1[simp] = p2pm1_to_mask
  shows "p \<notin> untyped_range cap
       \<Longrightarrow> in_device_frame p
              (trans_state (\<lambda>_. detype_ext (untyped_range cap) (exst s)) s
               \<lparr>kheap := \<lambda>x. if x \<in> untyped_range cap then None else kheap s x\<rparr>)
         = in_device_frame p s"
    using cap_is_valid untyped
    unfolding in_device_frame_def
    apply (cases cap; simp add: in_device_frame_def valid_untyped_def valid_cap_def obj_at_def)
    apply (rule iffI; erule exEI; elim conjE exE; simp)
    subgoal for dev ptr n f sz ko
      apply (elim allE; erule (1) impE)
      apply (drule valid_pspace_aligned[OF valid_pspace])
      apply (clarsimp simp: obj_range_def)
      apply (erule impE)
       apply (erule not_emptyI[rotated])
       apply (rule mask_in_range[THEN iffD1, simplified])
        apply (simp add: is_aligned_neg_mask)
       apply (simp add: mask_lower_twice)
      apply (cut_tac mask_in_range[THEN iffD1, simplified, OF is_aligned_neg_mask[OF le_refl] refl])
      apply fastforce
      done
    done

lemma pspace_respects_device_region_detype[detype_invs_proofs]:
  "pspace_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
  have "pspace_respects_device_region s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (intro pspace_respects_device_regionI)
    using pspace_aligned_detype valid_objs_detype invs
    apply (simp_all add: clear_um.pspace detype_def dom_def clear_um_def
                  split: if_split_asm )
       apply (drule pspace_respects_device_regionD[rotated -1],auto)+
    done
  qed

lemma cap_refs_respects_device_region_detype[detype_invs_proofs]:
  "cap_refs_respects_device_region (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
  have "cap_refs_respects_device_region s"
    using invs by (simp add: invs_def valid_state_def)
  thus ?thesis
    apply (clarsimp simp: clear_um_def cap_refs_respects_device_region_def
                simp del: split_paired_All split_paired_Ex)
    apply (drule_tac x = "(a,b)" in spec)
    apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_respects_device_region_def detype_def)
    done
  qed

lemma valid_machine_state_detype[detype_invs_proofs]:
    "valid_machine_state (clear_um (untyped_range cap) (detype (untyped_range cap) s))"
  proof -
    have "valid_machine_state s" using invs by (simp add: invs_def valid_state_def)
    thus ?thesis
    using untyped cap_is_valid
    by (clarsimp simp: valid_machine_state_def clear_um_def
      detype_def in_user_frame_eq in_device_frame_eq)
  qed

end

sublocale detype_locale < detype_locale_gen_2
 proof goal_cases
  interpret detype_locale_arch ..
  case 1 show ?case
  by (intro_locales; (unfold_locales; fact detype_invs_proofs)?)
  qed

context detype_locale begin
  lemmas invariants = invariants
  lemmas non_filter_detype = non_filter_detype
  lemmas valid_cap = valid_cap
  lemmas non_null_present = non_null_present
end

interpretation Detype_AI_2
  using detype_locale.invariants[simplified detype_locale_def]
        Detype_AI_2.intro
        by blast

context begin interpretation Arch .
lemma delete_objects_invs[wp]:
  "\<lbrace>(\<lambda>s. \<exists>slot. cte_wp_at ((=) (cap.UntypedCap dev ptr bits f)) slot s
    \<and> descendants_range (cap.UntypedCap dev ptr bits f) slot s) and
    invs and ct_active\<rbrace>
    delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (simp add: freeMemory_def word_size_def bind_assoc ef_storeWord)
   apply (rule hoare_pre)
   apply (rule_tac G="is_aligned ptr bits \<and> word_size_bits \<le> bits \<and> bits \<le> word_bits"
                in hoare_grab_asm)
   apply (simp add: mapM_storeWord_clear_um[unfolded word_size_def]
                    intvl_range_conv[where 'a=machine_word_len, folded word_bits_def])
   apply wp
  apply clarsimp
  apply (frule invs_untyped_children)
  apply (frule detype_invariants, clarsimp+)
  apply (drule invs_valid_objs)
  apply (drule (1) cte_wp_valid_cap)
  apply (simp add: valid_cap_def cap_aligned_def word_size_bits_def untyped_min_bits_def)
  done
end

end
