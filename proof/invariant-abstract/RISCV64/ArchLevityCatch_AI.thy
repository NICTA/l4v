(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchLevityCatch_AI
imports
  "ArchBCorres_AI"
  "Lib.LemmaBucket"
  "Lib.SplitRule"
begin

context Arch begin global_naming RISCV64

lemma asid_high_bits_of_shift[simp]:
  "asid_high_bits_of (ucast x << asid_low_bits) = x"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_eqI)
  apply (simp add: word_size nth_ucast nth_shiftr nth_shiftl asid_low_bits_def)
  done

lemma  ptrFormPAddr_addFromPPtr :
  "ptrFromPAddr (Platform.RISCV64.addrFromPPtr x) = x"
  by (simp add: ptrFromPAddr_def Platform.RISCV64.addrFromPPtr_def)


(****** From GeneralLib *******)

lemma asid_high_bits_of_add_ucast:
  "is_aligned w asid_low_bits \<Longrightarrow>
  asid_high_bits_of (ucast (x::9 word) + w) = asid_high_bits_of w"
  apply (rule word_eqI)
  apply (simp add: word_size asid_high_bits_of_def nth_ucast nth_shiftr is_aligned_nth)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: nth_ucast)
   apply (drule test_bit_size)
   apply (simp add: word_size asid_low_bits_def)
  apply (auto dest: test_bit_size simp: word_size asid_low_bits_def nth_ucast)
  done

lemma asid_high_bits_of_add:
  "\<lbrakk>is_aligned w asid_low_bits; x \<le> 2 ^ asid_low_bits - 1\<rbrakk>
   \<Longrightarrow> asid_high_bits_of (w + x) = asid_high_bits_of w"
  apply (rule word_eqI)
  apply (simp add: word_size asid_high_bits_of_def nth_ucast nth_shiftr
                   is_aligned_nth)
  apply (drule le2p_bits_unset, simp add: asid_low_bits_def word_bits_def)
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size)
   apply (case_tac "na < asid_low_bits")
    apply (simp add: asid_low_bits_def linorder_not_less word_bits_def)
  apply (auto dest: test_bit_size
              simp: asid_low_bits_def nth_ucast)
  done

lemma preemption_point_success [simp,intro]:
  "((Inr (), s') \<in> fst (preemption_point s)) \<Longrightarrow>
  \<exists>f es. s' = s \<lparr> machine_state := machine_state s \<lparr> irq_state := f (irq_state (machine_state s)) \<rparr>, exst := es \<rparr>"
  apply (auto simp: in_monad preemption_point_def do_machine_op_def
                    select_f_def select_def getActiveIRQ_def alternative_def
                    do_extended_op_def OR_choiceE_def mk_ef_def
             split: option.splits if_splits
             intro: exI[where x=id])
      apply (rule_tac x=Suc in exI, rule_tac x="exst bb" in exI, force)+
    apply (rule_tac x=id in exI, rule_tac x="exst b" in exI, force)+
    done

lemma pageBits_less_word_bits [simp]:
  "pageBits < word_bits" by (simp add: pageBits_def word_bits_conv)

lemma mask_out_8_le_kernel_base:
  "(x && ~~ mask 8 \<ge> kernel_base >> 20) = (x \<ge> kernel_base >> 20)"
  apply (rule iffI)
   apply (erule order_trans, rule word_and_le2)
  apply (drule_tac n=8 in neg_mask_mono_le)
  apply (simp add: kernel_base_def mask_def)
  done

lemma mask_out_8_less_kernel_base:
  "(x && ~~ mask 8 < kernel_base >> 20) = (x < kernel_base >> 20)"
  using mask_out_8_le_kernel_base[where x=x]
  by (simp add: linorder_not_less[symmetric])

lemma aobj_ref_arch_cap[simp]:
  "aobj_ref (arch_default_cap aty ptr us dev) = Some ptr"
  by (case_tac aty; simp add: arch_default_cap_def)

end
end
