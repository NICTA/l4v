(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before CRefine *)

theory ArchMove_C
imports "../Move_C"
begin

lemma word_shift_by_3:
  "x * 8 = (x::'a::len word) << 3"
  by (simp add: shiftl_t2n)

lemma unat_mask_3_less_8:
  "unat (p && mask 3 :: word64) < 8"
  apply (rule unat_less_helper)
  apply (rule order_le_less_trans, rule word_and_le1)
  apply (simp add: mask_def)
  done

definition
  user_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "user_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInUserData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"
definition
  device_word_at :: "machine_word \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "device_word_at x p \<equiv> \<lambda>s. is_aligned p 3
       \<and> pointerInDeviceData p s
       \<and> x = word_rcat (map (underlying_memory (ksMachineState s))
                                [p + 7, p + 6, p + 5, p + 4, p + 3, p + 2, p + 1, p])"

(* FIXME: move to GenericLib *)
lemmas unat64_eq_of_nat = unat_eq_of_nat[where 'a=64, folded word_bits_def]

context begin interpretation Arch .

(* FIXME RISCV: some 64-bit lemmas from X64's ArchMove_C will be needed here *)

crunch inv'[wp]: archThreadGet P

(* FIXME MOVE near thm tg_sp' *)
lemma atg_sp':
  "\<lbrace>P\<rbrace> archThreadGet f p \<lbrace>\<lambda>t. obj_at' (\<lambda>t'. f (tcbArch t') = t) p and P\<rbrace>"
  including no_pre
  apply (simp add: archThreadGet_def)
  apply wp
  apply (rule hoare_strengthen_post)
   apply (rule getObject_tcb_sp)
  apply clarsimp
  apply (erule obj_at'_weakenE)
  apply simp
  done

(* FIXME: MOVE to EmptyFail *)
lemma empty_fail_archThreadGet [intro!, wp, simp]:
  "empty_fail (archThreadGet f p)"
  by (simp add: archThreadGet_def getObject_def split_def)

(* FIXME: move to ainvs? *)
lemma sign_extend_canonical_address:
  "(x = sign_extend 38 x) = canonical_address x"
  by (fastforce simp: sign_extended_iff_sign_extend canonical_address_sign_extended canonical_bit_def)

end

end
