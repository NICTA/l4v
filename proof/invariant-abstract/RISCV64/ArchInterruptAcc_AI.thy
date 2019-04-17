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
 Arch-specific interrupt invariants
*)

theory ArchInterruptAcc_AI
imports "../InterruptAcc_AI"
begin

context Arch begin global_naming RISCV64

named_theorems InterruptAcc_AI_assms

lemma dmo_maskInterrupt_invs [InterruptAcc_AI_assms]:
  "\<lbrace>all_invs_but_valid_irq_states_for irq and (\<lambda>s. state = interrupt_states s irq)\<rbrace>
   do_machine_op (maskInterrupt (state = IRQInactive) irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: do_machine_op_def split_def maskInterrupt_def)
  apply wp
  apply (clarsimp simp: in_monad invs_def valid_state_def all_invs_but_valid_irq_states_for_def
                        valid_irq_states_but_def valid_irq_masks_but_def valid_machine_state_def
                        cur_tcb_def valid_irq_states_def valid_irq_masks_def)
  done

end

global_interpretation InterruptAcc_AI?: InterruptAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; fact InterruptAcc_AI_assms)
  qed

end
