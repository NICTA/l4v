(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory BCorres2_AI
imports
  "../../lib/BCorres_UL"
  "./$L4V_ARCH/ArchEmptyFail_AI"
begin

locale BCorres2_AI =
  fixes state  :: "'a::state_ext itself"
  assumes handle_arch_fault_reply_bcorres[wp]:
    "\<And>a b c d.
      bcorres (handle_arch_fault_reply a b c d :: 'a state \<Rightarrow> _)
              (handle_arch_fault_reply a b c d)"
  assumes arch_get_sanitise_register_info_bcorres[wp]:
    "\<And>t. bcorres (arch_get_sanitise_register_info t :: 'a state \<Rightarrow> _)
                  (arch_get_sanitise_register_info t)"
  assumes make_arch_fault_msg_bcorres[wp]:
    "\<And> a b.
      bcorres (make_arch_fault_msg a b :: 'a state \<Rightarrow> _)
              (make_arch_fault_msg a b)"
  assumes arch_switch_to_thread_bcorres[wp]:
    "\<And>t. bcorres (arch_switch_to_thread t :: 'a state \<Rightarrow> _)
        (arch_switch_to_thread t)"
  assumes arch_switch_to_idle_thread_bcorres[wp]:
    "bcorres (arch_switch_to_idle_thread :: 'a state \<Rightarrow> _)
        arch_switch_to_idle_thread"

definition all_but_exst where
"all_but_exst P \<equiv> (\<lambda>s. P (kheap s) (cdt s) (is_original_cap s)
                      (cur_thread s) (idle_thread s)
                      (consumed_time s) (cur_time s)
                      (cur_sc s) (reprogram_timer s)
                      (machine_state s) (interrupt_irq_node s)
                      (interrupt_states s) (arch_state s))"

lemma ef_mk_ef: "empty_fail f \<Longrightarrow> mk_ef (f s) = f s"
  apply (clarsimp simp add: empty_fail_def mk_ef_def)
  apply (drule_tac x=s in spec)
  apply (case_tac "f s")
  apply force
  done

lemma all_but_obvious: "all_but_exst (\<lambda>a b c d e f1 f2 f3 f4 f g h i.
                    x = \<lparr>kheap = a, cdt = b, is_original_cap = c,
                     cur_thread = d, idle_thread = e,
             consumed_time = f1, cur_time = f2,
cur_sc = f3, reprogram_timer = f4,
                     machine_state = f, interrupt_irq_node = g,
                     interrupt_states = h, arch_state = i, exst = (exst x)\<rparr>) x"
  apply (simp add: all_but_exst_def)
  done

lemma bluh: assumes a: "x =
        \<lparr>kheap = kheap ba, cdt = cdt ba,
           is_original_cap = is_original_cap ba,
           cur_thread = cur_thread ba, idle_thread = idle_thread ba,
           consumed_time = consumed_time ba, cur_time = cur_time ba,
           cur_sc = cur_sc ba, reprogram_timer = reprogram_timer ba,
           machine_state = machine_state ba,
           interrupt_irq_node = interrupt_irq_node ba,
           interrupt_states = interrupt_states ba,
           arch_state = arch_state ba, exst = exst x\<rparr>"
     shows "x\<lparr>exst := exst ba\<rparr> = ba"
  apply (subst a)
  apply simp
  done

lemma valid_cs_trans_state[simp]: "valid_cs a b (trans_state g s) = valid_cs a b s"
  by(simp add: valid_cs_def)

lemmas obj_at[simp] = more_update.obj_at_update[of a b g s for a b g s]

lemma valid_tcb_state[simp]: "valid_tcb_state a (trans_state g s) = valid_tcb_state a s"
  by (simp add: valid_tcb_state_def split: thread_state.splits option.splits)

lemma valid_bound_ntfn[simp]: "valid_bound_ntfn a (trans_state g s) = valid_bound_ntfn a s"
  by (simp add: valid_bound_obj_def split: option.splits)

lemma valid_bound_sc[simp]: "valid_bound_sc a (trans_state g s) = valid_bound_sc a s"
  by (simp add: valid_bound_obj_def split: option.splits)

lemma valid_arch_tcb_trans[simp]: "valid_arch_tcb t (trans_state g s) = valid_arch_tcb t s"
  by (auto elim: valid_arch_tcb_pspaceI)

lemma valid_tcb_trans_state[simp]: "valid_tcb a b (trans_state g s) = valid_tcb a b s"
  apply (simp add: valid_tcb_def)
  done

lemmas valid_bound_tcb[simp] = valid_bound_tcb_exst[of a g s for a g s]

lemma valid_ep_trans_state[simp]: "valid_ep a (trans_state g s) = valid_ep a s"
  apply (simp add: valid_ep_def split: endpoint.splits)
  done

lemma valid_ntfn_trans_state[simp]: "valid_ntfn a (trans_state g s) = valid_ntfn a s"
  apply (simp add: valid_ntfn_def split: ntfn.splits)
  done

lemma valid_sc_trans_state[simp]: "valid_sched_context a (trans_state g s) = valid_sched_context a s"
  apply (simp add: valid_sched_context_def)
  done

lemma valid_reply_trans_state[simp]: "valid_reply a (trans_state g s) = valid_reply a s"
  apply (simp add: valid_reply_def)
  done

lemma valid_obj_trans_state[simp]: "valid_obj a b (trans_state g s) = valid_obj a b s"
  apply (simp add: valid_obj_def
              split: kernel_object.splits option.splits)
  done

lemma dxo_ex: "((),x :: det_ext state) \<in> fst (do_extended_op f s) \<Longrightarrow>
       \<exists>e :: det_ext. x = (trans_state (\<lambda>_. e) s)"
  apply (clarsimp simp add: do_extended_op_def
                            bind_def gets_def in_monad
                            select_f_def mk_ef_def
                            trans_state_update'
                            wrap_ext_op_det_ext_ext_def)
  apply force
  done


locale is_extended' =
  fixes f :: "'a det_ext_monad"
  assumes a: "\<And>P. \<lbrace>all_but_exst P\<rbrace> f \<lbrace>\<lambda>_. all_but_exst P\<rbrace>"

context is_extended' begin

lemmas v = use_valid[OF _ a, OF _ all_but_obvious,simplified all_but_exst_def, THEN bluh]

lemma ex_st: "(a,x :: det_ext state) \<in> fst (f s) \<Longrightarrow>
       \<exists>e :: det_ext. x = (trans_state (\<lambda>_. e) s)"
  apply (drule v)
  apply (simp add: trans_state_update')
  apply (rule_tac x="exst x" in exI)
  apply simp
  done

lemmas all_but_exst[wp] = a[simplified all_but_exst_def]

lemma lift_inv: "(\<And>s g. P (trans_state g s) = P s) \<Longrightarrow>
       \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (clarsimp simp add: valid_def)
  apply (drule ex_st)
  apply force
  done

abbreviation (input) "I P \<equiv> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_.P\<rbrace>"

lemma obj_at[wp]: "I (obj_at a b)" by (rule lift_inv,simp)

lemma st_tcb_at[wp]: "I (st_tcb_at a b)" by (rule lift_inv,simp)

lemma valid_obj[wp]: "I (valid_obj a b)" by (rule lift_inv,simp)

lemma valid_pspace[wp]: "I (valid_pspace)" by (rule lift_inv,simp)

lemma valid_mdb[wp]: "I valid_mdb" by (rule lift_inv,simp)

lemma valid_ioc[wp]: "I valid_ioc" by (rule lift_inv,simp)

lemma valid_idle[wp]: "I valid_idle" by (rule lift_inv,simp)

lemma only_idle[wp]: "I only_idle" by (rule lift_inv,simp)

lemma if_unsafe_then_cap[wp]: "I if_unsafe_then_cap" by (rule lift_inv,simp)

lemma valid_global_refs[wp]: "I valid_global_refs" by (rule lift_inv,simp)

lemma valid_arch_state[wp]: "I valid_arch_state" by (rule lift_inv,simp)

lemma valid_irq_node[wp]: "I valid_irq_node" by (rule lift_inv,simp)

lemma valid_irq_handlers[wp]: "I valid_irq_handlers" by (rule lift_inv,simp)

lemma valid_machine_state[wp]: "I valid_machine_state" by (rule lift_inv,simp)

lemma valid_vspace_objs[wp]: "I valid_vspace_objs" by (rule lift_inv,simp)

lemma valid_arch_caps[wp]: "I valid_arch_caps" by (rule lift_inv,simp)

lemma valid_global_objs[wp]: "I valid_global_objs" by (rule lift_inv,simp)

lemma valid_global_vspace_mappings[wp]: "I valid_global_vspace_mappings" by (rule lift_inv,simp)

lemma valid_kernel_mappings[wp]: "I valid_kernel_mappings" by (rule lift_inv,simp)

lemma equal_kernel_mappings[wp]: "I equal_kernel_mappings" by (rule lift_inv,simp)

lemma valid_asid_map[wp]: "I valid_asid_map" by (rule lift_inv,simp)

lemma pspace_in_kernel_window[wp]: "I pspace_in_kernel_window" by (rule lift_inv,simp)

lemma cap_refs_in_kernel_window[wp]: "I cap_refs_in_kernel_window" by (rule lift_inv,simp)

lemma invs[wp]: "I invs" by (rule lift_inv,simp)

lemma cur_tcb[wp]: "I cur_tcb" by (rule lift_inv,simp)

lemma  valid_objs[wp]: "I (valid_objs)" by (rule lift_inv,simp)

lemma pspace_aligned[wp]: "I (pspace_aligned)" by (rule lift_inv,simp)

lemma pspace_distinct[wp]: "I (pspace_distinct)" by (rule lift_inv,simp)

lemma caps_of_state[wp]: "I (\<lambda>s. P (caps_of_state s))" by (rule lift_inv,simp)

lemma cte_wp_at[wp]: "I (\<lambda>s. P (cte_wp_at P' p s))" by (rule lift_inv,simp)

lemma no_cap_to_obj_dr_emp[wp]: "I (no_cap_to_obj_dr_emp x)" by (rule lift_inv,simp)

lemma valid_vs_lookup[wp]: "I (valid_vs_lookup)"
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (rule lift_inv, simp)
  qed

lemma typ_at[wp]: "I (\<lambda>s. P (typ_at T p s))" by (rule lift_inv,simp)

lemmas typ_ats[wp] = abs_typ_at_lifts [OF typ_at]

end


locale is_extended = is_extended' +
  constrains f :: "unit det_ext_monad"
  assumes b: "empty_fail f"

context is_extended begin

lemma dxo_eq[simp]:
  "do_extended_op f = f"
  apply (simp add: do_extended_op_def all_but_exst_def
                   get_def select_f_def modify_def put_def
                   wrap_ext_op_det_ext_ext_def ef_mk_ef[OF b])
  apply (rule ext)
  apply (simp add: bind_def)
  apply rule
   apply simp
   apply safe
     apply (simp | force | frule v)+
  done

end


lemma all_but_exst_update[simp]:
  "all_but_exst P (trans_state f s) = all_but_exst P s"
  apply (simp add: all_but_exst_def)
  done

crunch all_but_exst[wp]: set_scheduler_action,tcb_sched_action,
                         cap_move_ext "all_but_exst P"
  (simp: Let_def)

lemma next_domain_all_but_exst[wp]: "\<lbrace>all_but_exst P\<rbrace> next_domain \<lbrace>\<lambda>_. all_but_exst P\<rbrace>"
  sorry
(*crunch all_but_exst[wp]: next_domain "all_but_exst P"
  (simp: Let_def)*)

crunch (empty_fail) empty_fail[wp]: cap_move_ext

global_interpretation set_scheduler_action_extended: is_extended "set_scheduler_action a"
  by (unfold_locales; wp)

global_interpretation tcb_sched_action_extended: is_extended "tcb_sched_action a b"
  by (unfold_locales; wp)

global_interpretation next_domain_extended: is_extended "next_domain"
  by (unfold_locales; wp)

global_interpretation cap_move_ext: is_extended "cap_move_ext a b c d"
  by (unfold_locales; wp)


lemmas rec_del_simps_ext =
    rec_del.simps [THEN ext[where f="rec_del args" for args]]


lemma truncate_state_detype[simp]: "truncate_state (detype x s) = detype x (truncate_state s)"
  apply (simp add: detype_def trans_state_def)
  done

lemmas in_use_frame_truncate[simp] = more_update.in_user_frame_update[where f="\<lambda>_.()"]

lemma alternative_first:"x \<in> fst (f s) \<Longrightarrow> x \<in> fst ((f \<sqinter> g) s)"
  by (simp add: alternative_def)

lemma alternative_second:"x \<in> fst (g s) \<Longrightarrow> x \<in> fst ((f \<sqinter> g) s)"
  by (simp add: alternative_def)

lemma trans_state_twice[simp]: "trans_state (\<lambda>_. e) (trans_state f s) = trans_state (\<lambda>_. e) s"
  by (rule trans_state_update'')

lemma guarded_sub_switch: "((),x) \<in> fst (guarded_switch_to word s) \<Longrightarrow>
       \<exists>s'. ((),x) \<in> fst (switch_to_thread word s')
       \<and> (True, s') \<in> fst (is_schedulable word (in_release_queue word s) s)"
  apply (fastforce simp add: guarded_switch_to_def bind_def
                            get_thread_state_def
                            thread_get_def
                            in_monad)
  done

lemma truncate_state_updates[simp]:
  "truncate_state (scheduler_action_update f s) = truncate_state s"
  "truncate_state (ready_queues_update g s) = truncate_state s"
  by (rule trans_state_update'')+

lemma get_before_assert_opt:
  "do s \<leftarrow> assert_opt x; s' \<leftarrow> get; f s s' od
    = do s' \<leftarrow> get; s \<leftarrow> assert_opt x; f s s' od"
  apply (cases x, simp_all add: assert_opt_def)
  apply (simp add: ext exec_get)
  done

lemma get_outside_alternative:
  "alternative (get >>= f) g
    = do s \<leftarrow> get; alternative (f s) g od"
  by (simp add: alternative_def exec_get fun_eq_iff)

lemmas schedule_unfold_all = schedule_def allActiveTCBs_def
                        get_thread_state_def thread_get_def getActiveTCB_def

end
