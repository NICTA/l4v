(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory ArchKernelInit_AI
imports
  "../ADT_AI"
  "../Tcb_AI"
  "../Arch_AI"
begin

context Arch begin global_naming ARM (*FIXME: arch_split*)

text {*
  Showing that there is a state that satisfies the abstract invariants.
*}

lemma [simp]: "is_aligned (0x1000 :: word32) 9" by (simp add: is_aligned_def)
lemma [simp]: "is_aligned (0x2000 :: word32) 9" by (simp add: is_aligned_def)

lemmas ptr_defs = init_tcb_ptr_def idle_thread_ptr_def init_irq_node_ptr_def
                  init_globals_frame_def init_global_pd_def
lemmas state_defs = init_A_st_def init_kheap_def init_arch_state_def ptr_defs

lemma [simp]: "is_tcb (TCB t)" by (simp add: is_tcb_def)

lemma [simp]: "ran (empty_cnode n) = {Structures_A.NullCap}"
  apply (auto simp: ran_def empty_cnode_def)
  apply (rule_tac x="replicate n False" in exI)
  apply simp
  done

lemma empty_cnode_apply[simp]:
  "(empty_cnode n xs = Some cap) = (length xs = n \<and> cap = Structures_A.NullCap)"
  by (auto simp add: empty_cnode_def)

lemma valid_cs_size_empty[simp]:
  "valid_cs_size n (empty_cnode n) = (n < word_bits - cte_level_bits)"
  apply (simp add: valid_cs_size_def)
  apply (insert wf_empty_bits [of n])
  apply fastforce
  done

lemma init_cdt [simp]:
  "cdt init_A_st = init_cdt"
  by (simp add: state_defs)

lemma mdp_parent_empty [simp]:
  "\<not>empty \<Turnstile> x \<rightarrow> y"
  apply clarsimp
  apply (drule tranclD)
  apply (clarsimp simp: cdt_parent_of_def)
  done

lemma descendants_empty [simp]:
  "descendants_of x empty = {}"
  by (clarsimp simp: descendants_of_def)

lemma [simp]: "\<not>is_reply_cap Structures_A.NullCap"
  by (simp add: is_reply_cap_def)

lemma [simp]: "cap_range Structures_A.NullCap = {}"
  by (simp add: cap_range_def)

lemma pde_mapping_bits_shift:
  fixes x :: "12 word"
  shows "x \<noteq> 0 \<Longrightarrow> 2 ^ pde_mapping_bits - 1 < (ucast x << pde_mapping_bits :: word32)"
  apply (simp only:shiftl_t2n pde_mapping_bits_def)
  apply (unfold word_less_alt)
  apply simp
  apply (unfold word_mult_def)
  apply simp
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply simp
   apply (subst uint_up_ucast)
    apply (simp add: is_up_def source_size_def target_size_def word_size)
   apply (cut_tac 'a = "12" and x = x in uint_lt2p)
   apply simp
  apply (rule order_less_le_trans)
   prefer 2
   apply (rule pos_mult_pos_ge)
    apply (subst uint_up_ucast)
     apply (simp add: is_up_def source_size_def target_size_def word_size)
    apply (simp add: word_neq_0_conv word_less_alt)
   apply simp
  apply simp
  done

lemma mask_pde_mapping_bits:
  "mask 20 = 2^pde_mapping_bits - 1"
  by (simp add: mask_def pde_mapping_bits_def)



lemma init_irq_ptrs_ineqs:
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
proof -
  have P: "ucast irq < (2 ^ (14 - cte_level_bits) :: word32)"
    apply (rule order_le_less_trans[OF
        ucast_le_ucast[where 'a=10 and 'b=32,simplified,THEN iffD2, OF word_n1_ge]])
    apply (simp add: cte_level_bits_def minus_one_norm)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
    apply (rule is_aligned_no_wrap'[where sz=14])
     apply (simp add: is_aligned_def init_irq_node_ptr_def kernel_base_def)
    apply (rule shiftl_less_t2n[OF P])
    apply simp
    done
  show Q: "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric] add.assoc)
    apply (rule word_add_le_mono2)
     apply (simp only: trans [OF shiftl_t2n mult.commute])
     apply (rule nasty_split_lt[OF P])
      apply (simp_all add: cte_level_bits_def
        word_bits_def kernel_base_def init_irq_node_ptr_def)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric])
    apply (rule word_add_le_mono2)
     apply (rule minus_one_helper3, rule shiftl_less_t2n[OF P])
     apply simp
    apply (simp add: kernel_base_def
      cte_level_bits_def word_bits_def init_irq_node_ptr_def)
    done
qed

lemmas init_irq_ptrs_less_ineqs
   = init_irq_ptrs_ineqs(1)[THEN order_less_le_trans[rotated]]
     init_irq_ptrs_ineqs(2-3)[THEN order_le_less_trans]

lemmas init_irq_ptrs_all_ineqs[unfolded init_irq_node_ptr_def cte_level_bits_def]
   = init_irq_ptrs_ineqs(1)[THEN order_trans[rotated]]
     init_irq_ptrs_ineqs(2-3)[THEN order_trans]
     init_irq_ptrs_less_ineqs
     init_irq_ptrs_less_ineqs[THEN less_imp_neq]
     init_irq_ptrs_less_ineqs[THEN less_imp_neq, THEN not_sym]

lemmas ucast_le_ucast_10_32 = ucast_le_ucast[where 'a=10 and 'b=32,simplified]
lemma init_irq_ptrs_eq:
  "((ucast (irq :: irq) << cte_level_bits)
        = (ucast (irq' :: irq) << cte_level_bits :: word32))
      = (irq = irq')"
  apply safe
  apply (rule ccontr)
  apply (erule_tac bnd="ucast (max_word :: irq) + 1"
              in shift_distinct_helper[rotated 3],
         safe intro!: plus_one_helper2,
         simp_all add: ucast_le_ucast_10_32 up_ucast_inj_eq,
         simp_all add: cte_level_bits_def word_bits_def up_ucast_inj_eq
                       max_word_def)
  done

lemma in_kernel_base:
"\<lbrakk>m < 0xFFFFF; n \<le> 0xFFFFF\<rbrakk> \<Longrightarrow> (\<forall>y\<in>{kernel_base + m .. n + kernel_base}.
              kernel_base \<le> y \<and> y \<le> kernel_base + 0xFFFFF)"
  apply (clarsimp simp:)
  apply (intro conjI)
   apply (rule ccontr,simp add:not_le)
   apply (drule(1) le_less_trans)
   apply (cut_tac is_aligned_no_wrap'[where ptr = kernel_base and off = m
     and sz = 28,simplified])
     apply (drule(1) less_le_trans)
     apply simp
    apply (simp add:kernel_base_def is_aligned_def)
   apply (rule ccontr,simp add:not_less)
   apply (drule less_le_trans[where z = "0x10000000"])
    apply simp
   apply simp
  apply (erule order_trans)
  apply (simp add:field_simps)
  apply (rule word_plus_mono_right)
   apply simp
  apply (simp add:kernel_base_def)
  done

lemma pspace_aligned_init_A:
  "pspace_aligned init_A_st"
  apply (clarsimp simp: pspace_aligned_def state_defs wf_obj_bits [OF wf_empty_bits]
                        dom_if_Some cte_level_bits_def)
  apply (safe intro!: aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl],
           simp_all add: is_aligned_def word_bits_def kernel_base_def idle_sc_ptr_def
                         min_sched_context_bits_def)[1]
  done

lemma pspace_distinct_init_A:
  "pspace_distinct init_A_st"
  apply (clarsimp simp: pspace_distinct_def state_defs kernel_base_def cte_level_bits_def
                        linorder_not_le idle_sc_ptr_def)
  apply (safe, simp_all add: init_irq_ptrs_all_ineqs
                             [simplified kernel_base_def, simplified])[1]
        apply (cut_tac x="init_irq_node_ptr + (ucast irq << cte_level_bits)" and
                       y="init_irq_node_ptr + (ucast irqa << cte_level_bits)" and
                       sz=cte_level_bits
               in aligned_neq_into_no_overlap;
               simp add: init_irq_node_ptr_def kernel_base_def cte_level_bits_def)
          apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
          apply (simp add: is_aligned_def)
         apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
         apply (auto simp: is_aligned_def linorder_not_le min_sched_context_bits_def
                           init_irq_ptrs_all_ineqs(4)[simplified kernel_base_def, simplified])
  done


lemma caps_of_state_init_A_st_Null:
  "caps_of_state (init_A_st::'z::state_ext state) x
     = (if cte_at x (init_A_st::'z::state_ext state) then Some cap.NullCap else None)"
  apply (subgoal_tac "\<not> cte_wp_at (op \<noteq> cap.NullCap) x init_A_st")
   apply (auto simp add: cte_wp_at_caps_of_state)[1]
  apply (clarsimp, erule cte_wp_atE)
   apply (auto simp add: state_defs tcb_cap_cases_def split: if_split_asm)
  done

lemmas cte_wp_at_caps_of_state_eq
    = cte_wp_at_caps_of_state[where P="op = cap" for cap]

declare ptrFormPAddr_addFromPPtr[simp]

lemma pspace_respects_device_region_init[simp]:
  "pspace_respects_device_region init_A_st"
   apply (clarsimp simp: pspace_respects_device_region_def init_A_st_def init_machine_state_def device_mem_def
                         in_device_frame_def obj_at_def init_kheap_def a_type_def)
   apply (rule ext)
   apply clarsimp
   done

lemma cap_refs_respects_device_region_init[simp]:
  "cap_refs_respects_device_region init_A_st"
   apply (clarsimp simp: cap_refs_respects_device_region_def)
   apply (frule cte_wp_at_caps_of_state[THEN iffD1])
   apply clarsimp
   apply (subst(asm) caps_of_state_init_A_st_Null)
   apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_respects_device_region_def)
   done

lemma invs_A:
  "invs init_A_st"
  apply (simp add: invs_def)
  apply (rule conjI)
   prefer 2
   apply (simp add: cur_tcb_def state_defs obj_at_def idle_sc_ptr_def)
  apply (simp add: valid_state_def)
  apply (rule conjI)
   apply (simp add: valid_pspace_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_objs_def state_defs valid_obj_def valid_vm_rights_def
                          vm_kernel_only_def cte_level_bits_def idle_sc_ptr_def
                          valid_sched_context_def default_sched_context_def obj_at_def
                          valid_sched_context_size_def min_sched_context_bits_def
                          untyped_max_bits_def valid_tcb_def tcb_cap_cases_def
                          valid_ipc_buffer_cap_def valid_tcb_state_def is_sc_obj_def
                          valid_arch_tcb_def valid_cs_def word_bits_def)
   apply (rule conjI)
    apply (clarsimp simp: pspace_aligned_def state_defs
                          cte_level_bits_def idle_sc_ptr_def min_sched_context_bits_def)
    apply (safe intro!: aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl],
           simp_all add: is_aligned_def kernel_base_def)[1]
   apply (rule conjI)
    apply (clarsimp simp: pspace_distinct_init_A)
   apply (rule conjI)
    apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def state_defs)
    apply (rule conjI)
     apply (rule impI)
     apply (erule exE)
     apply (rule conjI)

      apply (rule impI)
      apply (subgoal_tac "kernel_base + 0x8000 + (UCAST(10 \<rightarrow> 32) irq << 4) \<noteq> ptr")
       apply (clarsimp simp: cte_level_bits_def)
      apply (rule init_irq_ptrs_all_ineqs(10))
      apply (clarsimp simp: kernel_base_def)

     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
      apply (subgoal_tac "kernel_base + 0x8000 + (UCAST(10 \<rightarrow> 32) irq << 4) \<noteq> ptr")
       apply (clarsimp simp: cte_level_bits_def)
      apply (rule init_irq_ptrs_all_ineqs(10))
      apply (clarsimp simp: kernel_base_def)

     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
      apply (subgoal_tac "kernel_base + 0x8000 + (UCAST(10 \<rightarrow> 32) irq << 4) \<noteq> ptr")
       apply (clarsimp simp: cte_level_bits_def)
      apply (rule init_irq_ptrs_all_ineqs(9))
      apply (clarsimp simp: kernel_base_def)

     apply (rule impI)
     apply (rule conjI)
      apply (rule impI)
      apply (subgoal_tac "kernel_base + 0x8000 + (UCAST(10 \<rightarrow> 32) irq << 4) \<noteq> ptr")
       apply (clarsimp simp: cte_level_bits_def)
      apply (rule init_irq_ptrs_all_ineqs(10))
      apply (clarsimp simp: idle_sc_ptr_def kernel_base_def)
     apply (clarsimp simp: live_def)

    apply (rule impI, rule conjI)+
      apply (clarsimp simp: idle_sc_ptr_def)
     apply clarsimp

(*
According to the current definition of "live", at the initial kernel state, the kernel objects
represented by cur_thread and cur_sc are live, which is not supposed to be. One of the assumptions
of this subgoal, "live (TCB blah blah)", is True as per the current definition of "live". This
makes proving this subgoal impossible or at least difficult.

A possible solution is to modify live_sc and live0 as follows,

live_sc sc \<equiv> (bound (sc_tcb sc) \<and> (sc_tcb sc) \<noteq> Some idle_thread_ptr
\<or> bound (sc_yield_from sc) \<or> bound (sc_ntfn sc) \<or> (sc_replies sc \<noteq> []))

live0 (TCB tcb) = (bound (tcb_bound_notification tcb)
                   \<or> tcb_state tcb \<noteq> IdleThreadState \<and> bound (tcb_sched_context tcb)
                   \<or> bound (tcb_yield_to tcb)
                   \<or> tcb_state tcb \<noteq> Inactive \<and> tcb_state tcb \<noteq> IdleThreadState)"
*)
  sorry

end

end
