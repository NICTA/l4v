(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory IpcDet_AI
imports "./$L4V_ARCH/ArchIpc_AI"
begin

crunch typ_at[wp]: send_ipc "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      send_ipc call bl w d cd t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma handle_fault_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault t f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: handle_fault_def unless_def handle_no_fault_def send_fault_ipc_def)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t tptr handler_cap fault can_donate.
    \<lbrace>tcb_at t :: det_ext state \<Rightarrow> bool\<rbrace>
      send_fault_ipc tptr handler_cap fault can_donate
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def)

lemma reply_push_idle_thread:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> reply_push caller callee reply_ptr can_donate \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  by (wpsimp simp: reply_push_def comp_def unbind_reply_in_ts_def no_reply_in_ts_def
               wp: hoare_drop_imp)

lemma receive_ipc_idle_thread[wp]:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace>
   receive_ipc thread cap is_blocking reply_cap \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  apply (simp add: receive_ipc_def)
  apply (case_tac cap; simp)
  apply (case_tac reply_cap; simp)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
   apply (rename_tac ep)
   apply (rule hoare_seq_ext[OF _ gbn_sp])
   apply (case_tac ntfnptr; simp)
    apply (case_tac ep; simp)
      apply (case_tac is_blocking; simp)
       apply wpsimp
      apply (wpsimp simp: do_nbrecv_failed_transfer_def)
     apply (wpsimp wp: hoare_drop_imp)
    apply (case_tac is_blocking; simp)
     apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
    apply (wpsimp simp: do_nbrecv_failed_transfer_def)
   apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
   apply (case_tac "isActive ntfn"; simp)
    apply (simp add: complete_signal_def)
    apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
    apply wpsimp
   apply (case_tac ep; simp)
  apply (wpsimp simp: do_nbrecv_failed_transfer_def)
    apply (wpsimp wp:  hoare_drop_imp)
   apply (wpsimp simp: sort_queue_def do_nbrecv_failed_transfer_def wp: mapM_wp_inv)
  apply wpsimp
        apply (wpsimp simp: complete_signal_def wp: hoare_drop_imp)
       apply (case_tac ep; simp)
         apply (wpsimp simp: sort_queue_def do_nbrecv_failed_transfer_def
                         wp: reply_push_idle_thread hoare_drop_imp mapM_wp_inv)+
  done

crunch cap_to[wp]: receive_ipc "ex_nonz_cap_to p :: det_ext state \<Rightarrow> bool"
  (wp: cap_insert_ex_cap hoare_drop_imps maybeM_inv simp: crunch_simps ignore: set_object)

lemma sort_queue_valid_ep_helper:
  "distinct list \<Longrightarrow> (a, b) \<in> set (zip list' list) \<Longrightarrow> (a', b) \<in> set (zip list' list) \<Longrightarrow> a = a'"
  apply (induct list arbitrary: list')
   apply clarsimp
  apply (clarsimp simp: zip_Cons)
  apply (erule disjE, fastforce dest!: in_set_zipE)
  apply (erule disjE, fastforce dest!: in_set_zipE, clarsimp)
  done

lemma sort_queue_valid_ep_RecvEP:
  "\<lbrace>valid_ep (RecvEP q)\<rbrace> sort_queue q \<lbrace>\<lambda>q'. valid_ep (RecvEP q')\<rbrace>"
  apply (clarsimp simp: valid_def valid_ep_def)
  apply (case_tac q; simp)
  apply (intro conjI)
    apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (erule disjE)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (erule in_set_zipE, clarsimp)
  apply (clarsimp simp: sort_queue_def return_def bind_def mapM_Cons)
  apply (clarsimp simp: distinct_map set_insort_key)
  apply (intro conjI)
    apply (fastforce simp: distinct_insort distinct_zipI2 dest!: in_set_zipE)
   apply (clarsimp simp: inj_on_def sort_queue_valid_ep_helper)
  apply (fastforce dest!: in_set_zipE)
  done

lemma sort_queue_valid_ep_SendEP:
  "\<lbrace>valid_ep (SendEP q)\<rbrace> sort_queue q \<lbrace>\<lambda>q'. valid_ep (SendEP q')\<rbrace>"
  apply (clarsimp simp: valid_def valid_ep_def)
  apply (case_tac q; simp)
  apply (intro conjI)
    apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (clarsimp simp: sort_queue_def mapM_Cons return_def bind_def)
   apply (erule disjE)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (rename_tac tptr list s')
   apply (erule_tac x = tptr in ballE)
    apply (rotate_tac -1)
    apply (frule use_valid[OF _ ethread_get_inv, where P = "tcb_at _"])
     apply fastforce
    apply (frule use_valid[OF _ mapM_wp_inv, where P = " tcb_at _"])
      apply wpsimp
     apply fastforce
    apply clarsimp
   apply (erule in_set_zipE, clarsimp)
  apply (clarsimp simp: sort_queue_def return_def bind_def mapM_Cons)
  apply (clarsimp simp: distinct_map set_insort_key)
  apply (intro conjI)
    apply (fastforce simp: distinct_insort distinct_zipI2 dest!: in_set_zipE)
   apply (clarsimp simp: inj_on_def sort_queue_valid_ep_helper)
  apply (fastforce dest!: in_set_zipE)
  done

lemma sort_queue_invs:
  "\<lbrace>invs\<rbrace> sort_queue q \<lbrace>\<lambda>q'. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
  done

lemma sort_queue_inv[wp]:
  "\<lbrace>P\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: sort_queue_def wp: mapM_wp_inv)
  done

lemma sort_queue_rv_wf:
  "\<lbrace>\<top>\<rbrace> sort_queue q \<lbrace>\<lambda>rv s. set rv = set q\<rbrace>"
  apply (clarsimp simp: valid_def sort_queue_def in_monad)
  apply (subgoal_tac "length prios = length q")
   apply (frule map_snd_zip)
   apply (simp add: image_set)
  apply (clarsimp simp: mapM_def)
  apply (induct q, clarsimp simp: sequence_def return_def)
  apply (clarsimp simp: sequence_def in_monad)
  done

lemma sort_queue_rv_wf'[wp]:
  "\<lbrace>P (set q)\<rbrace> sort_queue q \<lbrace>\<lambda>rv. P (set rv)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ sort_queue_rv_wf], simp, simp)
  apply (frule use_valid[OF _ sort_queue_inv, where P = "P (set q)"], simp+)
  done

lemma gt_reply_sp:
  "\<lbrace>P\<rbrace> get_reply_obj_ref reply_tcb rptr
   \<lbrace>\<lambda>t s. (\<exists>r. kheap s rptr = Some (Reply r) \<and> reply_tcb r = t) \<and> P s\<rbrace>"
  apply (wpsimp simp: get_sk_obj_ref_def get_simple_ko_def get_object_def)
  apply auto
  done

lemma cancel_ipc_st_tcb_at_active:
  "\<lbrace>\<lambda>s. invs s \<and> st_tcb_at active t' s \<and> t \<noteq> t'\<rbrace>
   cancel_ipc t \<lbrace>\<lambda>rv. st_tcb_at active t'\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (case_tac state; simp)
         apply wpsimp+
      apply (wpsimp wp: blocked_ipc_st_tcb_at_general)
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def st_tcb_at_def obj_at_def
                     split: option.splits)
      apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
      apply (clarsimp simp: tcb_st_refs_of_def split: thread_state.splits)
      apply (erule (1) pspace_valid_objsE)
      apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply obj_at_def
                            get_refs_def2 reply_tcb_reply_at_def)
     apply (wpsimp wp: blocked_ipc_st_tcb_at_general)
    apply (wpsimp simp: st_tcb_at_def obj_at_def invs_def valid_state_def valid_pspace_def
                    wp: reply_ipc_st_tcb_at_general)
    apply (frule (1) sym_refs_ko_atD[unfolded obj_at_def, simplified])
    apply (clarsimp simp: tcb_st_refs_of_def split: thread_state.splits)
    apply (erule (1) pspace_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def is_reply obj_at_def
                          get_refs_def2 reply_tcb_reply_at_def)
   apply (wpsimp wp: cancel_signal_st_tcb_at_general)
  apply wpsimp
  done

lemma ri_invs':
  fixes Q t cap is_blocking reply
  notes if_split[split del]
  notes hyp_refs_of_simps[simp del]
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes set_notification_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> complete_signal a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a (s::'a::state_ext state). \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes dit_Q: "\<And>a b c d e. \<lbrace>valid_mdb and valid_objs and Q\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes failed_transfer_Q[wp]: "\<And>a. \<lbrace>Q\<rbrace> do_nbrecv_failed_transfer a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sort_queue_Q[wp]: "\<And>q. \<lbrace>Q\<rbrace> sort_queue q \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes cancel_ipc_Q[wp]: "\<And>q. \<lbrace>invs and Q\<rbrace> cancel_ipc t \<lbrace>\<lambda>_. Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>(invs::det_ext state \<Rightarrow> bool) and Q and st_tcb_at active t and ex_nonz_cap_to t
         and cte_wp_at (op = cap.NullCap) (t, tcb_cnode_index 3)
         and (\<lambda>s. \<forall>r\<in>zobj_refs cap. ex_nonz_cap_to r s)\<rbrace>
     receive_ipc t cap is_blocking reply \<lbrace>\<lambda>r s. invs s \<and> Q s\<rbrace>" (is "\<lbrace>?pre\<rbrace> _ \<lbrace>_\<rbrace>")
  sorry

lemmas ri_invs[wp]
  = ri_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI,simplified]

lemma si_blk_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
   send_ipc True call bdg x can_donate t' epptr
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_ipc_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_inv])
  apply (case_tac ep; simp)
    apply (wpsimp wp: sts_st_tcb_at_cases)
   apply (wpsimp wp: sts_st_tcb_at_cases)
  apply (rule hoare_gen_asm[simplified])
  apply (rename_tac list)
  apply (case_tac list; simp)
  apply (rule hoare_seq_ext [OF _ set_simple_ko_pred_tcb_at])
  apply (rule hoare_seq_ext [OF _ gts_sp])
  apply (case_tac recv_state; simp)
  apply (wpsimp wp: sts_st_tcb_at_cases hoare_drop_imp)
    apply (intro conjI, wpsimp+)
   apply (intro conjI, wpsimp+)
  apply (clarsimp simp: st_tcb_at_def obj_at_def)
  apply (case_tac "tcb_state tcb"; simp)
  done

lemma sfi_makes_simple:
  "\<lbrace>st_tcb_at simple t and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace>
   send_fault_ipc t' handler_cap ft can_donate
   \<lbrace>\<lambda>rv. st_tcb_at simple t\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply (case_tac handler_cap; simp)
   apply wpsimp
  apply (wpsimp simp: thread_set_def set_object_def wp: si_blk_makes_simple)
  apply (auto simp: st_tcb_at_def obj_at_def)
  done

lemma hf_makes_simple:
  notes hoare_pre [wp_pre del]
  shows
  "\<lbrace>st_tcb_at simple t' and K (t \<noteq> t') :: det_ext state \<Rightarrow> bool\<rbrace> handle_fault t ft
   \<lbrace>\<lambda>rv. st_tcb_at simple t'\<rbrace>"
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb])
  apply (wpsimp simp: unless_def handle_no_fault_def send_fault_ipc_def wp: sts_st_tcb_at_cases)
  apply (case_tac "tcb_fault_handler tcb"; simp)
   apply wpsimp
  apply (wpsimp wp: si_blk_makes_simple)
  apply (wpsimp simp: thread_set_def set_object_def st_tcb_at_def obj_at_def)
  done

lemma si_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_. Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  notes dxo_wp_weak[wp del]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to ep and ex_nonz_cap_to t\<rbrace>
     send_ipc bl call ba cg can_donate t ep
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  sorry

lemma hf_invs':
  assumes set_endpoint_Q[wp]: "\<And>a b.\<lbrace>Q\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes sts_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes ext_Q[wp]: "\<And>a. \<lbrace>Q and valid_objs\<rbrace> possible_switch_to a \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes do_ipc_transfer_Q[wp]: "\<And>a b c d e. \<lbrace>Q and valid_objs and valid_mdb\<rbrace>
                                               do_ipc_transfer a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
  assumes thread_set_Q[wp]: "\<And>a b. \<lbrace>Q\<rbrace> thread_set a b \<lbrace>\<lambda>_.Q\<rbrace>"
  notes si_invs''[wp] = si_invs'[where Q=Q]
  shows
  "\<lbrace>invs and Q and st_tcb_at active t and ex_nonz_cap_to t and (\<lambda>_. valid_fault f)\<rbrace>
   handle_fault t f
   \<lbrace>\<lambda>r (s::det_ext state). invs s \<and> Q s\<rbrace>"
  including no_pre
  apply (cases "valid_fault f"; simp)
  apply (simp add: handle_fault_def)
  apply (rule hoare_seq_ext[OF _ assert_get_tcb_sp])
   apply (wpsimp simp: handle_no_fault_def unless_def)
    apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
                    wp: sts_only_idle valid_irq_node_typ)
   apply (simp add: send_fault_ipc_def)
   apply (case_tac "tcb_fault_handler tcb"; simp)
                apply (wpsimp simp: invs_def valid_state_def valid_pspace_def)
                apply (fastforce simp: st_tcb_at_def obj_at_def state_refs_of_def get_refs_def2
                                       tcb_st_refs_of_def idle_no_ex_cap
                                elim!: delta_sym_refs
                                split: if_splits thread_state.splits)
               apply wpsimp
              apply (intro conjI)
               apply (wpsimp simp: tcb_cap_cases_def
                               wp: thread_set_invs_trivial thread_set_no_change_tcb_state
                                   ex_nonz_cap_to_pres thread_set_cte_wp_at_trivial)
                  apply (simp (no_asm) add: ex_nonz_cap_to_def cte_wp_at_cases2)
                  apply (rule_tac x = t in exI)
                  apply (rule_tac x = "tcb_cnode_index 3" in exI)
                  apply (clarsimp simp: obj_at_def tcb_cnode_map_def)
                 apply wpsimp+
  done

lemmas hf_invs[wp] = hf_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI,simplified]

end
