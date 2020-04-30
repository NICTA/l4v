(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchBCorres2_AI
imports
  "../BCorres2_AI"
begin

context Arch begin global_naming X64

named_theorems BCorres2_AI_assms

crunch (bcorres)bcorres[wp, BCorres2_AI_assms]: invoke_cnode truncate_state
  (simp: swp_def ignore: clearMemory without_preemption filterM ethread_set)

crunch (bcorres)bcorres[wp]: create_cap,init_arch_objects,retype_region,delete_objects truncate_state
  (ignore: freeMemory clearMemory retype_region_ext)

crunch (bcorres)bcorres[wp]: set_extra_badge,derive_cap truncate_state (ignore: storeWord)

crunch (bcorres)bcorres[wp]: invoke_untyped truncate_state
  (ignore: sequence_x)

crunch (bcorres)bcorres[wp]: set_mcpriority truncate_state

crunch (bcorres)bcorres[wp, BCorres2_AI_assms]: arch_get_sanitise_register_info, arch_post_modify_registers truncate_state

crunch (bcorres)bcorres[wp]: updateIRQState truncate_state

lemma invoke_tcb_bcorres[wp]:
  fixes a
  shows "bcorres (invoke_tcb a) (invoke_tcb a)"
  apply (cases a)
        apply (wp | wpc | simp add: set_mcpriority_def)+
  apply (rename_tac option)
  apply (case_tac option)
   apply (wp | wpc | simp)+
  done

lemma transfer_caps_loop_bcorres[wp]:
 "bcorres (transfer_caps_loop ep buffer n caps slots mi) (transfer_caps_loop ep buffer n caps slots mi)"
  apply (induct caps arbitrary: slots n mi ep)
   apply simp
   apply wp
  apply (case_tac a)
  apply simp
  apply (intro impI conjI)
             apply (wp | simp)+
  done

lemma invoke_irq_control_bcorres[wp]: "bcorres (invoke_irq_control a) (invoke_irq_control a)"
  apply (cases a)
  apply (wp | simp add: arch_invoke_irq_control_def | wpc)+
  done

lemma invoke_irq_handler_bcorres[wp]: "bcorres (invoke_irq_handler a) (invoke_irq_handler a)"
  apply (cases a)
  apply (wp | simp)+
  done

lemma make_arch_fault_msg_bcorres[wp,BCorres2_AI_assms]:
  "bcorres (make_arch_fault_msg a b) (make_arch_fault_msg a b)"
  by (cases a; simp ; wp)

lemma  handle_arch_fault_reply_bcorres[wp,BCorres2_AI_assms]:
  "bcorres ( handle_arch_fault_reply a b c d) (handle_arch_fault_reply a b c d)"
  by (cases a; simp add: handle_arch_fault_reply_def; wp)

crunch (bcorres)bcorres[wp, BCorres2_AI_assms]:
    arch_switch_to_thread,arch_switch_to_idle_thread truncate_state

end

interpretation BCorres2_AI?: BCorres2_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact BCorres2_AI_assms)?)
  qed

lemmas schedule_bcorres[wp] = schedule_bcorres1[OF BCorres2_AI_axioms]

context Arch begin global_naming X64

crunch (bcorres)bcorres[wp]: send_ipc,send_signal,do_reply_transfer,arch_perform_invocation truncate_state
  (simp: gets_the_def swp_def set_object_def
 ignore: freeMemory clearMemory loadWord cap_fault_on_failure
         storeWord lookup_error_on_failure getRestartPC getRegister mapME )

lemma perform_invocation_bcorres[wp]: "bcorres (perform_invocation a b c) (perform_invocation a b c)"
  apply (cases c)
  apply (wp | wpc | simp)+
  done

lemma decode_cnode_invocation[wp]: "bcorres (decode_cnode_invocation a b c d) (decode_cnode_invocation a b c d)"
  apply (simp add: decode_cnode_invocation_def)
  apply (wp | wpc | simp add: split_def | intro impI conjI)+
  done

crunch (bcorres)bcorres[wp]:
  decode_set_ipc_buffer, decode_set_space, decode_set_priority,
  decode_set_mcpriority, decode_set_sched_params, decode_bind_notification,
  decode_unbind_notification, decode_set_tls_base truncate_state

lemma decode_tcb_configure_bcorres[wp]: "bcorres (decode_tcb_configure b (cap.ThreadCap c) d e)
     (decode_tcb_configure b (cap.ThreadCap c) d e)"
  apply (simp add: decode_tcb_configure_def | wp)+
  done

lemma decode_tcb_invocation_bcorres[wp]:"bcorres (decode_tcb_invocation a b (cap.ThreadCap c) d e) (decode_tcb_invocation a b (cap.ThreadCap c) d e)"
  apply (simp add: decode_tcb_invocation_def)
  apply (wp | wpc | simp)+
  done

lemma create_mapping_entries_bcorres[wp]: "bcorres (create_mapping_entries a b c d e f) (create_mapping_entries a b c d e f)"
  apply (cases c)
  apply (wp | simp)+
  done

lemma ensure_safe_mapping_bcorres[wp]: "bcorres (ensure_safe_mapping a) (ensure_safe_mapping a)"
  apply (induct rule: ensure_safe_mapping.induct)
  apply (wp | wpc | simp)+
  done

crunch (bcorres) bcorres[wp]: handle_invocation truncate_state
  (simp: syscall_def Let_def gets_the_def
   ignore: syscall cap_fault_on_failure without_preemption const_on_failure
           decode_tcb_invocation)

crunch (bcorres)bcorres[wp]: receive_ipc,receive_signal,delete_caller_cap truncate_state

lemma handle_vm_fault_bcorres[wp]: "bcorres (handle_vm_fault a b) (handle_vm_fault a b)"
  unfolding handle_vm_fault_def
  apply (cases b)
  apply (simp | wp)+
  done

lemma handle_hypervisor_fault_bcorres[wp]: "bcorres (handle_hypervisor_fault a b) (handle_hypervisor_fault a b)"
  by (cases b) wpsimp

lemma handle_event_bcorres[wp]: "bcorres (handle_event e) (handle_event e)"
  apply (cases e)
  apply (simp add: handle_send_def handle_call_def handle_recv_def handle_reply_def handle_yield_def
                   handle_interrupt_def Let_def handle_reserved_irq_def arch_mask_irq_signal_def
         | intro impI conjI allI | wp | wpc)+
  done

crunch (bcorres)bcorres[wp]: guarded_switch_to,switch_to_idle_thread truncate_state (ignore: storeWord)

lemma choose_switch_or_idle:
  "((), s') \<in> fst (choose_thread s) \<Longrightarrow>
       (\<exists>word. ((),s') \<in> fst (guarded_switch_to word s)) \<or>
       ((),s') \<in> fst (switch_to_idle_thread s)"
  apply (simp add: choose_thread_def)
  apply (clarsimp simp add: switch_to_idle_thread_def bind_def gets_def
                   arch_switch_to_idle_thread_def in_monad
                   return_def get_def modify_def put_def
                    get_thread_state_def
                   thread_get_def
                   split: if_split_asm)
  apply force
  done

end

end
