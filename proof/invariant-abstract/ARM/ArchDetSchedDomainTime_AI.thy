(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ArchDetSchedDomainTime_AI
imports "../DetSchedDomainTime_AI"
begin

context Arch begin global_naming ARM

named_theorems DetSchedDomainTime_AI_assms

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_list s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects, arch_tcb_set_ipc_buffer,
  arch_invoke_irq_control, handle_vm_fault, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, make_arch_fault_msg,
  arch_post_modify_registers, arch_post_cap_deletion
  "\<lambda>s. P (domain_list s)"

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_finalise_cap "\<lambda>s. P (domain_time s)"
  (wp: hoare_drop_imps mapM_wp subset_refl simp: crunch_simps)

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]:
  arch_activate_idle_thread, arch_switch_to_thread, arch_switch_to_idle_thread,
  handle_arch_fault_reply, init_arch_objects, arch_tcb_set_ipc_buffer,
  arch_invoke_irq_control, handle_vm_fault, arch_get_sanitise_register_info,
  prepare_thread_delete, handle_hypervisor_fault, make_arch_fault_msg,
  arch_post_modify_registers, arch_post_cap_deletion
  "\<lambda>s. P (domain_time s)"

end

global_interpretation DetSchedDomainTime_AI?: DetSchedDomainTime_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

context Arch begin global_naming ARM

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps check_cap_inv)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: arch_perform_invocation "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps check_cap_inv)

lemma handle_interrupt_valid_domain_time [DetSchedDomainTime_AI_assms]:
  "\<lbrace>\<lambda>s :: det_ext state. 0 < domain_time s \<rbrace> handle_interrupt i
   \<lbrace>\<lambda>rv s.  domain_time s = 0 \<longrightarrow> scheduler_action s = choose_new_thread \<rbrace>"
   apply (unfold handle_interrupt_def)
   apply (case_tac "maxIRQ < i"; simp)
    subgoal by (wp hoare_false_imp, simp)
   apply (rule hoare_pre)
    apply (wp do_machine_op_exst | simp | wpc)+
       apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
       apply wp
      apply (rule_tac Q="\<lambda>_ s. 0 < domain_time s" in hoare_post_imp, fastforce)
      apply wp+
     apply simp (* dxo_eq *)
     apply (clarsimp simp: num_domains_def)
     apply (wp reschedule_required_valid_domain_time
           | simp add: handle_reserved_irq_def
           | wp_once hoare_drop_imp)+
    apply clarsimp
   done

crunch domain_time_inv [wp, DetSchedDomainTime_AI_assms]: handle_reserved_irq "\<lambda>s. P (domain_time s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

crunch domain_list_inv [wp, DetSchedDomainTime_AI_assms]: handle_reserved_irq "\<lambda>s. P (domain_list s)"
  (wp: crunch_wps mapM_wp subset_refl simp: crunch_simps ignore: make_fault_msg)

end

global_interpretation DetSchedDomainTime_AI_2?: DetSchedDomainTime_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact DetSchedDomainTime_AI_assms)?)
  qed

end
