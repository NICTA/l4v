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
VSpace refinement
*)

theory VSpacePre_AI
imports "$L4V_ARCH/ArchTcbAcc_AI"
begin

context begin interpretation Arch .

requalify_facts
  cap_master_cap_tcb_cap_valid_arch

end

lemma throw_on_false_wp[wp]:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (rv \<longrightarrow> Q () s) \<and> (\<not> rv \<longrightarrow> E x s)\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> throw_on_false x f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (simp add: throw_on_false_def unlessE_def)
  apply wp
   apply simp
  apply simp
  done

crunch_ignore (add: throw_on_false)

definition
  "is_arch_update cap cap' \<equiv> is_arch_cap cap \<and> cap_master_cap cap = cap_master_cap cap'"


definition
  "is_arch_diminished cap cap' \<equiv> is_arch_cap cap \<and> diminished cap cap'"


lemma dmo_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply simp
  done

crunch caps_of_state[wp]: do_machine_op "\<lambda>s. P (caps_of_state s)"

interpretation dmo: non_vspace_non_cap_op "do_machine_op f"
  by (unfold_locales; wp)

declare not_Some_eq_tuple[simp]

lemma valid_irq_states_arch_state_update[simp]:
  "valid_irq_states (s\<lparr>arch_state := x\<rparr>) = valid_irq_states s"
  by(auto simp: valid_irq_states_def)

lemma pull_out_P:
  "P s \<and> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> Q s c) \<longrightarrow> (\<forall>c. caps_of_state s p = Some c \<longrightarrow> P s \<and> Q s c)"
  by blast

lemma upto_enum_step_subtract:
  "x \<le> z \<Longrightarrow> [x, y .e. z] = (map ((op +) x) [0, y - x .e. z - x])"
  by (auto simp add: upto_enum_step_def)

(* FIXME: move *)
lemma returnOk_E': "\<lbrace>P\<rbrace> returnOk r -,\<lbrace>E\<rbrace>"
  by (clarsimp simp: returnOk_def validE_E_def validE_def valid_def return_def)
lemma throwError_R': "\<lbrace>P\<rbrace> throwError e \<lbrace>Q\<rbrace>,-"
  by (clarsimp simp:throwError_def validE_R_def validE_def valid_def return_def)

lemma invs_valid_irq_states[elim!]:
  "invs s \<Longrightarrow> valid_irq_states s"
  by(auto simp: invs_def valid_state_def)

lemma bool_function_four_cases:
  "f = Not \<or> f = id \<or> f = (\<lambda>_. True) \<or> f = (\<lambda>_. False)"
  by (auto simp add: fun_eq_iff all_bool_eq)

lemma uint_ucast:
  "(x :: ('a :: len) word) < 2 ^ len_of TYPE ('b)
    \<Longrightarrow> uint (ucast x :: ('b :: len) word) = uint x"
  apply (simp add: ucast_def)
  apply (subst word_uint.Abs_inverse)
   apply (simp add: uints_num word_less_alt word_le_def)
   apply (frule impI[where P="True"])
   apply (subst(asm) uint_2p)
    apply (clarsimp simp only: word_neq_0_conv[symmetric])
   apply simp_all
  done

(* FIXME: move *)
lemma inj_on_domD: "\<lbrakk>inj_on f (dom f); f x = Some z; f y = Some z\<rbrakk> \<Longrightarrow> x = y"
  by (erule inj_onD) clarsimp+

lemma hoare_name_pre_state2:
  "(\<And>s. \<lbrace>P and (op = s)\<rbrace> f \<lbrace>Q\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: valid_def intro: hoare_name_pre_state)

lemma pd_casting_shifting:
  "size x + n < len_of TYPE('a) \<Longrightarrow>
     ucast (ucast x << n >> n :: ('a :: len) word) = x"
  apply (rule word_eqI)
  apply (simp add: nth_ucast nth_shiftr nth_shiftl word_size)
  done

lemma aligned_already_mask:
  "is_aligned x n \<Longrightarrow> is_aligned (x && msk) n"
  apply (simp add: is_aligned_mask word_bw_assocs)
  apply (subst word_bw_comms, subst word_bw_assocs[symmetric])
  apply simp
  done

lemma set_upto_enum_step_4:
  "set [0, 4 .e. x :: word32]
       = (\<lambda>x. x << 2) ` {.. x >> 2}"
  by (auto simp: upto_enum_step_def shiftl_t2n shiftr_div_2n_w
                 word_size mult.commute)

lemma set_upto_enum_step_8:
  "set [0, 8 .e. x :: word32]
       = (\<lambda>x. x << 3) ` {.. x >> 3}"
  by (auto simp: upto_enum_step_def shiftl_t2n shiftr_div_2n_w
                 word_size mult.commute)

lemma arch_update_cap_zombies:
  "\<lbrace>\<lambda>s. cte_wp_at (is_arch_update cap) p s \<and> zombies_final s\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. zombies_final s\<rbrace>"
  apply (simp add: zombies_final_def2 cte_wp_at_caps_of_state del: split_paired_All)
  apply wp
  apply (intro allI impI)
  apply (elim conjE exE)
  apply (simp del: split_paired_All add: is_arch_update_def split: if_split_asm)
    apply (erule_tac x=p in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (frule master_cap_obj_refs)
    apply (drule cap_master_cap_zombie)
    apply clarsimp
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p in allE)
   apply simp
   apply (frule master_cap_obj_refs)
   apply (drule cap_master_cap_zombie)
   apply clarsimp
  done

lemma arch_update_cap_pspace:
  "\<lbrace>cte_wp_at (is_arch_update cap) p and valid_pspace and valid_cap cap\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs update_cap_iflive arch_update_cap_zombies)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def)
  apply (frule cap_master_cap_zobj_refs)
  apply clarsimp
  apply (drule caps_of_state_cteD)
  apply (drule (1) cte_wp_tcb_cap_valid)
  apply (simp add: cap_master_cap_tcb_cap_valid_arch)
  done

lemma arch_update_cap_valid_mdb:
  "\<lbrace>cte_wp_at (is_arch_update cap) p and valid_mdb\<rbrace> set_cap cap p \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply (simp add: valid_mdb_def2 pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=cdt])
   prefer 2
   apply wp[1]
  apply (rule hoare_lift_Pf2 [where f=is_original_cap])
   prefer 2
   apply wp[1]
  apply (rule hoare_pre)
   apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: mdb_cte_at_def is_arch_update_def)
   apply (fastforce simp: is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: untyped_mdb_def is_arch_update_def)
   apply (rule conjI)
    apply (fastforce simp: is_cap_simps)
   apply clarsimp
   apply (drule master_cap_obj_refs)
   apply fastforce
  apply (rule conjI)
   apply (erule(1) descendants_inc_minor)
   apply (clarsimp simp:is_arch_update_def)
   apply (frule master_cap_class)
   apply (clarsimp dest!:master_cap_cap_range)
  apply (rule conjI)
   apply (clarsimp simp: untyped_inc_def is_arch_update_def)
  subgoal by (fastforce simp: is_cap_simps)
  apply (rule conjI)
   apply (clarsimp simp: ut_revocable_def)
   apply (clarsimp simp: is_arch_update_def is_cap_simps)
  apply (clarsimp simp: irq_revocable_def is_arch_update_def is_cap_simps simp del: split_paired_All)
  done

lemma set_cap_arch_obj:
  "\<lbrace>ko_at (ArchObj ao) p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. ko_at (ArchObj ao) p\<rbrace>"
  apply (wp set_cap_obj_at_other)
  apply (clarsimp simp: obj_at_def cte_wp_at_cases)
  done

lemma set_mrs_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_mrs t buf mrs \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_mrs_def zipWithM_x_mapM split_def
                   store_word_offs_def set_object_def
              cong: option.case_cong
              split del: if_split)
  apply (wp hoare_vcg_split_case_option)
    apply (rule mapM_wp [where S=UNIV, simplified])
    apply (wp | simp)+
  apply (clarsimp simp: obj_at_def a_type_def
                  dest!: get_tcb_SomeD)
  done

lemma set_mrs_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ, wp)


lemma set_mrs_ntfn_at[wp]:
  "\<lbrace> ntfn_at p \<rbrace> set_mrs receiver recv_buf mrs \<lbrace>\<lambda>rv. ntfn_at p \<rbrace>"
  by (simp add: ntfn_at_typ, wp)

end
