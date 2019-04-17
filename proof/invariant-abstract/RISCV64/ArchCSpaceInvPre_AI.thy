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
CSpace invariants
*)

theory ArchCSpaceInvPre_AI
imports "../CSpaceInvPre_AI"
begin

context Arch begin global_naming RISCV64

lemma aobj_ref_acap_rights_update[simp]:
  "aobj_ref (acap_rights_update f x) = aobj_ref x"
  by (cases x; simp add: acap_rights_update_def)

lemma arch_obj_size_acap_rights_update[simp]:
  "arch_obj_size (acap_rights_update f x) = arch_obj_size x"
  by (cases x; simp add: acap_rights_update_def)

lemma valid_arch_cap_acap_rights_update[intro]:
  "valid_arch_cap x s \<Longrightarrow> valid_arch_cap (acap_rights_update f x) s"
  by (cases x; simp add: acap_rights_update_def valid_arch_cap_def)

definition cap_master_arch_cap :: "arch_cap \<Rightarrow> arch_cap" where
  "cap_master_arch_cap acap \<equiv>
     (case acap of
           ASIDPoolCap pool asid \<Rightarrow> ASIDPoolCap pool 0
         | FrameCap ptr R sz dev _ \<Rightarrow> FrameCap ptr UNIV sz dev None
         | PageTableCap ptr _ \<Rightarrow> PageTableCap ptr None
         | _ \<Rightarrow> acap)"

lemma cap_master_arch_cap_eqDs1:
  "cap_master_arch_cap cap = ASIDPoolCap pool asid
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ASIDPoolCap pool asid)"
  "cap_master_arch_cap cap = ASIDControlCap \<Longrightarrow> cap = ASIDControlCap"
  "cap_master_arch_cap cap = FrameCap ptr R sz dev map_data
     \<Longrightarrow> R = UNIV \<and> map_data = None
          \<and> (\<exists>R map_data. cap = FrameCap ptr R sz dev map_data)"
  "cap_master_arch_cap cap = PageTableCap ptr data
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = PageTableCap ptr data)"
  by (clarsimp simp: cap_master_arch_cap_def split: arch_cap.split_asm)+

lemma cap_master_arch_inv[simp]:
  "cap_master_arch_cap (cap_master_arch_cap ac) = cap_master_arch_cap ac"
  by (cases ac; simp add: cap_master_arch_cap_def)

definition
  "is_ap_cap cap \<equiv> case cap of ArchObjectCap (ASIDPoolCap _ _) \<Rightarrow> True | _ \<Rightarrow> False"

lemmas is_ap_cap_simps [simp] = is_ap_cap_def [split_simps cap.split arch_cap.split]

definition is_frame_cap :: "cap \<Rightarrow> bool" where
  "is_frame_cap cap \<equiv> arch_cap_fun_lift is_FrameCap False cap"

definition
  "reachable_target \<equiv> \<lambda>(asid, vref) p s.
     \<exists>level. vs_lookup_target level asid vref s = Some (level, p)"

definition
  "reachable_frame_cap cap \<equiv> \<lambda>s.
     is_frame_cap cap \<and> (\<exists>ref. vs_cap_ref cap = Some ref \<and> reachable_target ref (obj_ref_of cap) s)"

abbreviation
  "same_vspace_table_cap_type c c' \<equiv>
      is_pt_cap c \<and> is_pt_cap c'
    \<or> is_frame_cap c \<and> is_frame_cap c'"

(* The conditions under which it is legal to immediately replace an arch_cap
   cap with newcap at slot sl, assuming cap is final. *)
definition
  replaceable_final_arch_cap :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "replaceable_final_arch_cap s sl newcap \<equiv> \<lambda>cap.
    (* Don't leave dangling vspace references. That is, if cap points to a mapped vspace object, *)
    (\<forall>ref. vs_cap_ref cap = Some ref
             (* then either newcap maintains the same chain of vs_refs, *)
            \<longrightarrow> (vs_cap_ref newcap = Some ref \<and> obj_refs newcap = obj_refs cap)
             (* or the object pointed to by cap is not currently mapped. *)
              \<or> (\<forall>oref \<in> obj_refs cap. \<not> reachable_target ref oref s)
    (* Don't introduce duplicate caps to vspace table objects with different vs_ref chains. *)
  \<and> no_cap_to_obj_with_diff_ref newcap {sl} s
    (* Don't introduce non-empty unmapped table objects. *)
  \<and> (is_pt_cap newcap
      \<longrightarrow> cap_asid newcap = None
      \<longrightarrow> (\<forall>r \<in> obj_refs newcap. pts_of s r = Some empty_pt))
    (* If newcap is vspace table cap such that either:
         - newcap and cap have different types or different obj_refs, or
         - newcap is unmapped while cap is mapped, *)
  \<and> (is_pt_cap newcap
         \<longrightarrow> (is_pt_cap newcap
                  \<longrightarrow> (cap_asid newcap = None \<longrightarrow> cap_asid cap = None)
                  \<longrightarrow> obj_refs cap \<noteq> obj_refs newcap)
    (* then, aside from sl, there is no other slot with a cap that
         - has the same obj_refs and type as newcap, and
         - is unmapped if newcap is mapped. *)
         \<longrightarrow> (\<forall>sl'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs newcap
                     \<and> (same_vspace_table_cap_type newcap cap')
                     \<and> (cap_asid newcap = None \<or> cap_asid cap' = None)) sl' s \<longrightarrow> sl' = sl))
  (* Don't replace with an ASID pool. *)
  \<and> \<not>is_ap_cap newcap)"

definition
  replaceable_non_final_arch_cap :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "replaceable_non_final_arch_cap s sl newcap \<equiv> \<lambda>cap. \<not> reachable_frame_cap cap s"

declare
  replaceable_final_arch_cap_def[simp]
  replaceable_non_final_arch_cap_def[simp]

lemma unique_table_refsD:
  "\<lbrakk> unique_table_refs_2 cps; cps p = Some cap; cps p' = Some cap';
     obj_refs cap = obj_refs cap'\<rbrakk>
     \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  unfolding unique_table_refs_def
  by blast

lemma table_cap_ref_vs_cap_ref_Some:
  "table_cap_ref x = Some y \<Longrightarrow> vs_cap_ref x = Some y"
  by (clarsimp simp: table_cap_ref_def vs_cap_ref_def table_cap_ref_arch_def vs_cap_ref_arch_def
                 split: cap.splits arch_cap.splits)

lemma set_cap_aobjs_of[wp]:
  "set_cap cap ptr \<lbrace>\<lambda>s. P (aobjs_of s)\<rbrace>"
  sorry (* FIXME RISCV *)

lemma set_cap_valid_vs_lookup:
  "\<lbrace>\<lambda>s. valid_vs_lookup s
      \<and> (\<forall>vref cap'. caps_of_state s ptr = Some cap'
                \<longrightarrow> vs_cap_ref cap' = Some vref
                \<longrightarrow> (vs_cap_ref cap = Some vref \<and> obj_refs cap = obj_refs cap')
                 \<or> (\<not> is_final_cap' cap' s \<and> \<not> reachable_frame_cap cap' s)
                 \<or> (\<forall>oref. oref \<in> obj_refs cap' \<longrightarrow> \<not> reachable_target vref oref s))
      \<and> unique_table_refs s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def
              del: split_paired_All split_paired_Ex)
  sorry (* FIXME RISCV
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_convert_imp[OF set_cap.vs_lookup_pages]
             hoare_vcg_disj_lift)
  apply (elim conjE allEI, rule impI, drule(1) mp)
  apply (simp only: simp_thms)
  apply (elim exE conjE)
  apply (case_tac "p' = ptr")
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (elim disjE impCE)
     apply fastforce
    apply clarsimp
    apply (drule (1) not_final_another_caps)
     apply (erule obj_ref_is_gen_obj_ref)
    apply (simp, elim exEI, clarsimp simp: gen_obj_refs_eq)
    apply (rule conjI, clarsimp)
    apply (drule(3) unique_table_refsD)
    apply (clarsimp simp: reachable_pg_cap_def is_pg_cap_def)
    apply (case_tac cap, simp_all add: vs_cap_ref_simps)[1]
    apply (rename_tac arch_cap)
    apply (case_tac arch_cap,
           simp_all add: vs_cap_ref_simps table_cap_ref_simps)[1]
       apply (clarsimp dest!: table_cap_ref_vs_cap_ref_Some)
      apply fastforce
     apply (clarsimp dest!: table_cap_ref_vs_cap_ref_Some)+
  apply (auto simp: cte_wp_at_caps_of_state)[1]
  done *)

lemma set_cap_valid_table_caps:
  "\<lbrace>\<lambda>s. valid_table_caps s \<and>
        (is_pt_cap cap \<longrightarrow> cap_asid cap = None \<longrightarrow> (\<forall>r \<in> obj_refs cap. pts_of s r = Some empty_pt))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (wp hoare_vcg_all_lift
            hoare_vcg_disj_lift hoare_convert_imp[OF set_cap_caps_of_state]
            hoare_use_eq[OF set_cap_arch set_cap_obj_at_impossible])
  sorry (* FIXME: RISCV
  apply (simp add: empty_table_caps_of)
  done *)

lemma set_cap_unique_table_caps:
  "\<lbrace>\<lambda>s. unique_table_caps s
      \<and> (is_pt_cap cap
             \<longrightarrow> (\<forall>oldcap. caps_of_state s ptr = Some oldcap
                    \<longrightarrow> is_pt_cap oldcap
                    \<longrightarrow> (cap_asid cap = None \<longrightarrow> cap_asid oldcap = None)
                    \<longrightarrow> obj_refs oldcap \<noteq> obj_refs cap)
             \<longrightarrow> (\<forall>ptr'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs cap
                                              \<and> is_pt_cap cap'
                                              \<and> (cap_asid cap = None \<or> cap_asid cap' = None)) ptr' s \<longrightarrow> ptr' = ptr))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>_. unique_table_caps\<rbrace>"
  apply wp
  sorry (* FIXME RISCV
  apply (simp only: unique_table_caps_def)
  apply (elim conjE)
  apply (erule impCE)
   apply clarsimp
  apply (erule impCE)
   prefer 2
   apply (simp del: imp_disjL)
   apply (thin_tac "\<forall>a b. P a b" for P)
   apply (auto simp: cte_wp_at_caps_of_state)[1]
  apply (clarsimp simp del: imp_disjL del: allI)
  apply (case_tac "cap_asid cap \<noteq> None")
   apply (clarsimp del: allI)
   apply (elim allEI | rule impI)+
   subgoal by (auto simp: is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def)
  apply (elim allEI)
  apply (intro conjI impI)
   apply (elim allEI)
   subgoal by (auto simp: is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def)
  apply (elim allEI)
  subgoal by (auto simp: is_pt_cap_def is_pd_cap_def is_pdpt_cap_def is_pml4_cap_def)
  done *)

lemma set_cap_unique_table_refs:
  "\<lbrace>\<lambda>s. unique_table_refs s
      \<and> no_cap_to_obj_with_diff_ref cap {ptr} s\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. unique_table_refs\<rbrace>"
  apply wp
  apply clarsimp
  apply (simp add: unique_table_refs_def
              split del: if_split del: split_paired_All)
  apply (erule allEI, erule allEI)
  apply (clarsimp split del: if_split)
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state
                 split: if_split_asm)
  done

lemma set_cap_valid_arch_caps:
  "\<lbrace>\<lambda>s. valid_arch_caps s
      \<and> (\<forall>vref cap'. cte_wp_at ((=) cap') ptr s
                \<longrightarrow> vs_cap_ref cap' = Some vref
                \<longrightarrow> (vs_cap_ref cap = Some vref \<and> obj_refs cap = obj_refs cap')
                 \<or> (\<not> is_final_cap' cap' s \<and> \<not> reachable_frame_cap cap' s)
                 \<or> (\<forall>oref \<in> obj_refs cap'. \<not> reachable_target vref oref s))
      \<and> no_cap_to_obj_with_diff_ref cap {ptr} s
      \<and> (is_pt_cap cap \<longrightarrow> cap_asid cap = None
            \<longrightarrow> (\<forall>r \<in> obj_refs cap. pts_of s r = Some empty_pt))
      \<and> (is_pt_cap cap
             \<longrightarrow> (\<forall>oldcap. caps_of_state s ptr = Some oldcap \<longrightarrow>
                  is_pt_cap oldcap
                    \<longrightarrow> (cap_asid cap = None \<longrightarrow> cap_asid oldcap = None)
                    \<longrightarrow> obj_refs oldcap \<noteq> obj_refs cap)
             \<longrightarrow> (\<forall>ptr'. cte_wp_at (\<lambda>cap'. obj_refs cap' = obj_refs cap
                     \<and> is_pt_cap cap'
                     \<and> (cap_asid cap = None \<or> cap_asid cap' = None)) ptr' s \<longrightarrow> ptr' = ptr))\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  sorry (* FIXME RISCV
  by (simp add: valid_arch_caps_def pred_conj_def;
      wp set_cap_valid_vs_lookup set_cap_valid_table_caps
         set_cap_unique_table_caps set_cap_unique_table_refs;
      clarsimp simp: cte_wp_at_def) *)

lemma valid_table_capsD:
  "\<lbrakk> cte_wp_at ((=) cap) ptr s; valid_table_caps s; is_pt_cap cap; cap_asid cap = None \<rbrakk>
   \<Longrightarrow> \<forall>r \<in> obj_refs cap. pts_of s r = Some empty_pt"
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_table_caps_def is_pt_cap_def
                        is_PageTableCap_def cap_asid_def
                 split: option.splits)
   apply (cases ptr, fastforce)+
  done

lemma pt_caps_asid_vsref:
  "is_pt_cap cap \<Longrightarrow> (cap_asid cap = None) = (vs_cap_ref cap = None)"
  apply (cases cap; simp)
  apply (rename_tac acap, case_tac acap; simp add: cap_asid_def split: option.splits)
  done

lemma unique_table_capsD:
  "\<lbrakk> unique_table_caps_2 cps; cps ptr = Some cap; cps ptr' = Some cap';
     obj_refs cap = obj_refs cap'; vs_cap_ref cap = None \<or> vs_cap_ref cap' = None;
     is_pt_cap cap; is_pt_cap cap' \<rbrakk>
     \<Longrightarrow> ptr = ptr'"
  unfolding unique_table_caps_def
  by blast

lemma valid_refs_def2:
  "valid_refs R s = (\<forall>p c. caps_of_state s p = Some c \<longrightarrow> cap_range c \<inter> R = {})"
  by (auto simp: valid_refs_def cte_wp_at_caps_of_state)

lemma set_cap_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window and (\<lambda>s. \<forall>ref \<in> cap_range cap. ref \<in> kernel_window s)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: cap_refs_in_kernel_window_def valid_refs_def2
                   pred_conj_def)
  apply (rule hoare_lift_Pf2[where f=arch_state])
   apply wp
  sorry (* FIXME RISCV
   apply (fastforce elim!: ranE split: if_split_asm)
  apply wp
  done *)

lemma cap_refs_in_kernel_windowD:
  "\<lbrakk> caps_of_state s ptr = Some cap; cap_refs_in_kernel_window s \<rbrakk>
   \<Longrightarrow> \<forall>ref \<in> cap_range cap. ref \<in> kernel_window s"
  apply (clarsimp simp: cap_refs_in_kernel_window_def valid_refs_def
                        cte_wp_at_caps_of_state)
  sorry (* FIXME RISCV
  apply (cases ptr, fastforce)
  done *)

lemma valid_cap_imp_valid_vm_rights:
  "valid_cap (ArchObjectCap (FrameCap p rs sz dev m)) s \<Longrightarrow> rs \<in> valid_vm_rights"
  by (simp add: valid_cap_def valid_vm_rights_def)

lemma acap_rights_update_idem [simp]:
  "acap_rights_update R (acap_rights_update R' cap) = acap_rights_update R cap"
  by (simp add: acap_rights_update_def split: arch_cap.splits)

lemma cap_master_arch_cap_rights [simp]:
  "cap_master_arch_cap (acap_rights_update R cap) = cap_master_arch_cap cap"
  by (simp add: cap_master_arch_cap_def acap_rights_update_def
           split: arch_cap.splits)

lemma acap_rights_update_id [intro!, simp]:
  "valid_arch_cap ac s \<Longrightarrow> acap_rights_update (acap_rights ac) ac = ac"
  unfolding acap_rights_update_def acap_rights_def valid_arch_cap_def
  by (cases ac; simp)

lemma obj_ref_none_no_asid:
  "{} = obj_refs new_cap \<longrightarrow> None = table_cap_ref new_cap"
  "obj_refs new_cap = {} \<longrightarrow> table_cap_ref new_cap = None"
  sorry (* FIXME RISCV
  by (simp add: table_cap_ref_def split: cap.split arch_cap.split)+ *)

lemma set_cap_hyp_refs_of [wp]:
 "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
  set_cap cp p
  \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (auto elim!: rsubst[where P=P]
               simp: state_hyp_refs_of_def obj_at_def
             intro!: ext
             split: if_split_asm)
  done

lemma state_hyp_refs_of_revokable[simp]:
  "state_hyp_refs_of (s \<lparr> is_original_cap := m \<rparr>) = state_hyp_refs_of s"
  by (rule revokable_update.state_hyp_refs_update)

lemma is_valid_vtable_root_is_arch_cap:
  "is_valid_vtable_root cap \<Longrightarrow> is_arch_cap cap"
  by (clarsimp simp: is_valid_vtable_root_def is_arch_cap_def split: cap.splits)

end
end
