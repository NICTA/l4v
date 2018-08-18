(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory TcbAcc_AI
imports "$L4V_ARCH/ArchCSpace_AI"
begin

context begin interpretation Arch .

requalify_facts
  valid_arch_arch_tcb_context_set
  state_hyp_refs_of_tcb_sched_context_update
  state_hyp_refs_of_tcb_yield_to_update
  global_refs_kheap
end

declare global_refs_kheap[simp]

locale TcbAcc_AI_storeWord_invs =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes storeWord_invs[wp]:
    "\<And> p w.
      \<lbrace>in_user_frame p and invs :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_machine_op (storeWord p w)
      \<lbrace>\<lambda>rv. invs\<rbrace>"

(* FIXME: move to Invariatns? *)
lemma symreftype_inverse':
  "symreftype ref = ref' \<Longrightarrow> ref = symreftype ref'"
  by (cases ref) simp_all

lemmas gts_inv[wp] = get_thread_state_inv

lemmas gbn_inv[wp] = get_tcb_obj_ref_inv

lemma gts_sp:
  "\<lbrace>P\<rbrace> get_thread_state t \<lbrace>\<lambda>st. st_tcb_at (\<lambda>x. st = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gts_st_tcb)
   apply (rule gts_inv)
  apply simp
  done

lemma gbn_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_bound_notification t \<lbrace>\<lambda>ntfn. bound_tcb_at (\<lambda>x. ntfn = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbn_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma gsc_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_sched_context t \<lbrace>\<lambda>sc. bound_sc_tcb_at (\<lambda>x. sc = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbsc_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma gyt_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_yield_to t \<lbrace>\<lambda>sc. bound_yt_tcb_at (\<lambda>x. sc = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbyt_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma red_univ_get_wp[simp]:
  "(\<forall>(rv, s') \<in> fst (f s). s = s' \<longrightarrow> (rv, s') \<in> fst (f s'))"
  by clarsimp


lemma thread_get_inv [wp]: "\<lbrace>P\<rbrace> thread_get f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: thread_get_def | wp)+

locale TcbAcc_AI_arch_tcb_context_set_eq =
  assumes arch_tcb_context_set_eq[simp]:
    "\<And> t. arch_tcb_context_set (arch_tcb_context_get t) t = t"

lemma (in TcbAcc_AI_arch_tcb_context_set_eq) thread_get_as_user:
  "thread_get (arch_tcb_context_get o tcb_arch) t = as_user t get"
  apply (simp add: thread_get_def as_user_def)
  apply (rule bind_cong [OF refl])
  apply (clarsimp simp: gets_the_member)
  apply (simp add: get_def the_run_state_def set_object_def
                   put_def bind_def return_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: map_upd_triv select_f_def image_def)
  done

lemma thread_set_as_user:
  "thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_context_set (f $ arch_tcb_context_get (tcb_arch tcb)) (tcb_arch tcb) \<rparr>) t
    = as_user t (modify f)"
proof -
  have P: "\<And>f. det (modify f)"
    by (simp add: modify_def)
  thus ?thesis
    apply (simp add: as_user_def P thread_set_def)
    apply (clarsimp simp add: select_f_def simpler_modify_def bind_def image_def)
    done
qed

lemma ball_tcb_cap_casesI:
  "\<lbrakk> P (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>));
     P (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>));
     P (tcb_ipcframe, tcb_ipcframe_update, (\<lambda>_ _. is_nondevice_page_cap or (op = cap.NullCap)));
     P (tcb_fault_handler, tcb_fault_handler_update, (\<lambda>_ _. is_ep_cap or (op = NullCap)));
     P (tcb_timeout_handler, tcb_timeout_handler_update, (\<lambda>_ _. is_ep_cap or (op = NullCap))) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cap_cases. P x"
  by (simp add: tcb_cap_cases_def)


lemma thread_set_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> thread_set f p' \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def a_type_def)
  done


lemma thread_set_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> thread_set t' f \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: thread_set_typ_at [where P="\<lambda>s. s"] tcb_at_typ)

lemma thread_set_no_change_tcb_pred:
  assumes x: "\<And>tcb. proj (tcb_to_itcb (f tcb))    = proj (tcb_to_itcb tcb)"
  shows      "\<lbrace>pred_tcb_at proj P t\<rbrace> thread_set f t' \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: thread_set_def pred_tcb_at_def)
  apply wp
   apply (rule set_object_at_obj)
  apply wp
  apply (clarsimp simp: obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: x)
  done

lemmas thread_set_no_change_tcb_state=thread_set_no_change_tcb_pred[where proj="itcb_state",simplified]

lemmas thread_set_no_change_tcb_bound_notification = thread_set_no_change_tcb_pred[where proj="itcb_bound_notification", simplified]

lemmas thread_set_no_change_tcb_sched_context =
   thread_set_no_change_tcb_pred[where proj="itcb_sched_context", simplified]

lemmas thread_set_no_change_tcb_yield_to =
   thread_set_no_change_tcb_pred[where proj="itcb_yield_to", simplified]

lemma thread_set_no_change_tcb_pred_converse:
  assumes x: "\<And>tcb. proj (tcb_to_itcb (f tcb)) = proj (tcb_to_itcb tcb)"
  shows      "\<lbrace>\<lambda>s. \<not> pred_tcb_at proj P t s\<rbrace> thread_set f t' \<lbrace>\<lambda>rv s. \<not> pred_tcb_at proj P t s\<rbrace>"
  apply (clarsimp simp: thread_set_def pred_tcb_at_def set_object_def in_monad
                        gets_the_def valid_def)
  apply (erule notE)
  apply (clarsimp simp: obj_at_def split: if_split_asm)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: x)
  done

lemmas thread_set_no_change_tcb_state_converse=
  thread_set_no_change_tcb_pred_converse[where proj="itcb_state", simplified]

lemmas thread_set_no_change_tcb_bound_notification_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_bound_notification", simplified]

lemmas thread_set_no_change_tcb_sched_context_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_sched_context", simplified]

lemmas thread_set_no_change_tcb_yield_to_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_yield_to", simplified]

lemma pspace_valid_objsE:
  assumes p: "kheap s p = Some ko"
  assumes v: "valid_objs s"
  assumes Q: "\<lbrakk>kheap s p = Some ko; valid_obj p ko s\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
proof -
  from p have "ko_at ko p s" by (simp add: obj_at_def)
  with v show Q by (auto elim: obj_at_valid_objsE simp: Q)
qed

lemma thread_set_split_out_sset_tcb_obj_ref:
  assumes f: "\<forall>tcb. (tcb_bound_notification_update (\<lambda>_. tcb_bound_notification (f arbitrary)) (f tcb))
                        = f tcb"
  shows "thread_set f t
      = (do thread_set (\<lambda>tcb. (f tcb) \<lparr> tcb_bound_notification := tcb_bound_notification tcb \<rparr>) t;
            set_tcb_obj_ref tcb_bound_notification_update t (tcb_bound_notification (f arbitrary))
         od)"
  apply (simp add: thread_set_def set_object_is_modify set_tcb_obj_ref_def bind_assoc)
  apply (rule ext)
  apply (clarsimp simp: simpler_modify_def bind_def
                        gets_the_def simpler_gets_def
                        assert_opt_def fail_def return_def
                 split: option.split)
  apply (auto dest!: get_tcb_SomeD, auto simp: get_tcb_def f)
  done (* is this used anywhere? *)

schematic_goal tcb_ipcframe_in_cases:
  "(tcb_ipcframe, ?x) \<in> ran tcb_cap_cases"
  by (fastforce simp add: ran_tcb_cap_cases)


lemmas valid_ipc_buffer_cap_simps= valid_ipc_buffer_cap_def[split_simps cap.split]

locale TcbAcc_AI_valid_ipc_buffer_cap_0 =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes valid_ipc_buffer_cap_0[simp]:
    "\<And>cap buf. valid_ipc_buffer_cap cap buf \<Longrightarrow> valid_ipc_buffer_cap cap 0"
  assumes thread_set_hyp_refs_trivial:
    "(\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb) \<Longrightarrow>
        (\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb) \<Longrightarrow>
         \<lbrace>\<lambda>(s::'state_ext state). P (state_hyp_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"


context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma thread_set_valid_objs_triv:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (f tcb) = tcb_ipc_buffer tcb
                        \<or> (tcb_ipc_buffer (f tcb) = 0)"
  assumes a: "\<And>tcb. tcb_fault (f tcb) \<noteq> tcb_fault tcb
                       \<longrightarrow> (case tcb_fault (f tcb) of None \<Rightarrow> True
                                                   | Some f \<Rightarrow> valid_fault f)"
  assumes b: "\<And>tcb. tcb_bound_notification (f tcb) \<noteq> tcb_bound_notification tcb
                       \<longrightarrow> tcb_bound_notification (f tcb) = None"
  assumes b': "\<And>tcb. tcb_sched_context (f tcb) \<noteq> tcb_sched_context tcb
                       \<longrightarrow> tcb_sched_context (f tcb) = None"
  assumes b'': "\<And>tcb. tcb_yield_to(f tcb) \<noteq> tcb_yield_to tcb
                       \<longrightarrow> tcb_yield_to (f tcb) = None"
  assumes c: "\<And>tcb s::'z::state_ext state.
                     valid_arch_tcb (tcb_arch (f tcb)) s = valid_arch_tcb (tcb_arch tcb) s"
  shows "\<lbrace>valid_objs\<rbrace> thread_set f t \<lbrace>\<lambda>rv. valid_objs :: 'z::state_ext state \<Rightarrow> bool\<rbrace>"
  using bspec [OF x, OF tcb_ipcframe_in_cases]
  apply (simp add: thread_set_def)
  apply wp
   apply (rule set_object_valid_objs)
  apply wp
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def valid_bound_obj_def z
                            split_paired_Ball obj_at_def c
                            a_type_def bspec_split[OF x])
  apply (rule conjI)
   apply (elim allEI)
   apply auto[1]
  apply (rule conjI)
   apply (cut_tac tcb = y in w)
   apply (auto simp: valid_ipc_buffer_cap_simps)[1]
  apply (cut_tac tcb=y in a)
  apply (cut_tac tcb=y in b)
  apply (cut_tac tcb=y in b')
  apply (cut_tac tcb=y in b'')
  by auto[1]

end


lemma thread_set_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_aligned)
  apply (clarsimp simp: a_type_def)
  done


lemma thread_set_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_distinct)
  apply clarsimp
  done


lemma thread_set_cur_tcb:
  shows "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def)
  apply (clarsimp simp: thread_set_def pred_tcb_at_def set_object_def in_monad
                        gets_the_def valid_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def is_tcb)
  done

lemma thread_set_iflive_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes w: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  assumes a: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>if_live_then_nonz_cap\<rbrace> thread_set f t \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_iflive)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def get_tcb_def
                        split_paired_Ball
                        bspec_split [OF x])
  apply (subgoal_tac "live (TCB y)")
   apply (fastforce elim: if_live_then_nonz_capD2)
  apply (clarsimp simp: live_def hyp_live_tcb_def z y w t a)
  done


lemma thread_set_ifunsafe_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>if_unsafe_then_cap\<rbrace> thread_set f t \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_ifunsafe)
  apply (clarsimp simp: x)
  done


lemma thread_set_zombies_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>zombies_final\<rbrace> thread_set f t \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: thread_set_def)
  apply wp
  apply (clarsimp simp: x)
  done


(* FIXME-NTFN: possible need for assumption on tcb_bound_notification *)
lemma thread_set_refs_trivial:
  assumes x: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes w: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  shows      "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: state_refs_of_def get_tcb_def x y w t
                 elim!: rsubst[where P=P]
                intro!: ext)
  done


lemma thread_set_valid_idle_trivial:
  assumes "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  assumes "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  shows      "\<lbrace>valid_idle\<rbrace> thread_set f t \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def valid_idle_def)
  apply wp
  apply (clarsimp simp: assms get_tcb_def pred_tcb_at_def obj_at_def)
  done


crunch it [wp]: thread_set "\<lambda>s. P (idle_thread s)"

crunch arch [wp]: thread_set "\<lambda>s. P (arch_state s)"


lemma thread_set_caps_of_state_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp elim!: rsubst[where P=P]
                 intro!: ext
                  dest!: get_tcb_SomeD)
  apply (subst caps_of_state_after_update)
   apply (clarsimp simp: obj_at_def get_tcb_def bspec_split [OF x])
  apply simp
  done



crunch irq_node[wp]: thread_set "\<lambda>s. P (interrupt_irq_node s)"


lemma thread_set_global_refs_triv:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>valid_global_refs\<rbrace> thread_set f t \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (rule valid_global_refs_cte_lift)
     apply (wp thread_set_caps_of_state_trivial x)+
  done

crunch interrupt_states[wp]: thread_set "\<lambda>s. P (interrupt_states s)"

lemma thread_set_obj_at_impossible:
  "\<lbrakk> \<And>tcb. \<not> (P (TCB tcb)) \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. obj_at P p s\<rbrace> thread_set f t \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def)
  done


lemma tcb_not_empty_table:
  "\<not> empty_table S (TCB tcb)"
  by (simp add: empty_table_def)
(*
lemmas thread_set_arch_caps_trivial
  = valid_arch_caps_lift_weak[OF thread_set_arch thread_set.aobj_at
                                 thread_set_caps_of_state_trivial, simplified] *)
lemmas thread_set_arch_caps_trivial
  = valid_arch_caps_lift_weak[OF thread_set_arch thread_set.vsobj_at
                                 thread_set_caps_of_state_trivial, simplified]

lemma thread_set_only_idle:
  "\<lbrace>only_idle and K (\<forall>tcb. tcb_state (f tcb) = tcb_state tcb \<or> \<not>idle (tcb_state (f tcb)))\<rbrace>
  thread_set f t \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)
  apply (drule get_tcb_SomeD)
  apply force
  done


lemma thread_set_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_pspace_in_kernel_window)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

crunch pspace_respects_device_region[wp]: thread_set "pspace_respects_device_region"
  (wp: set_object_pspace_respects_device_region)

lemma thread_set_cap_refs_in_kernel_window:
  assumes y: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> thread_set f t \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_cap_refs_in_kernel_window)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (drule bspec[OF y])
  apply simp
  apply (erule sym)
  done

lemma thread_set_cap_refs_respects_device_region:
  assumes y: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows
  "\<lbrace>cap_refs_respects_device_region\<rbrace> thread_set f t \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_cap_refs_respects_device_region)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (drule bspec[OF y])
  apply simp
  apply (erule sym)
  done

(* NOTE: The function "thread_set f p" updates a TCB at p using function f.
   It should not be used to change capabilities, though. *)
lemma thread_set_valid_ioc_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>valid_ioc\<rbrace> thread_set f p \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: thread_set_def, wp set_object_valid_ioc_caps)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (cut_tac tcb=y in x)
  apply (clarsimp simp: cte_wp_at_cases get_tcb_def cap_of_def null_filter_def
                        split_def tcb_cnode_map_tcb_cap_cases
                 split: option.splits Structures_A.kernel_object.splits)
  apply (drule_tac x="(get,set,restr)" in bspec)
   apply (fastforce simp: ranI)+
  done

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma thread_set_invs_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z:  "\<And>tcb. tcb_state     (f tcb) = tcb_state tcb"
  assumes z': "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes y: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (f tcb) = tcb_ipc_buffer tcb
                        \<or> (tcb_ipc_buffer (f tcb) = 0)"
  assumes a: "\<And>tcb. tcb_fault (f tcb) \<noteq> tcb_fault tcb
                       \<longrightarrow> (case tcb_fault (f tcb) of None \<Rightarrow> True
                                                   | Some f \<Rightarrow> valid_fault f)"
  assumes arch: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>invs::'state_ext state \<Rightarrow> bool\<rbrace> thread_set f t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_weaken_pre)
   apply (wp thread_set_valid_objs_triv
             thread_set_refs_trivial
             thread_set_hyp_refs_trivial
             thread_set_iflive_trivial
             thread_set_mdb
             thread_set_ifunsafe_trivial
             thread_set_cur_tcb
             thread_set_zombies_trivial
             thread_set_valid_idle_trivial
             thread_set_global_refs_triv
             thread_set_valid_ioc_trivial
             valid_irq_node_typ valid_irq_handlers_lift
             thread_set_caps_of_state_trivial
             thread_set_arch_caps_trivial thread_set_only_idle
             thread_set_cap_refs_in_kernel_window
             thread_set_cap_refs_respects_device_region
             thread_set_aligned
             | rule x z z' y w t a arch valid_tcb_arch_ref_lift [THEN fun_cong]
             | erule bspec_split [OF x] | simp add: z' y t)+
  apply (simp add: z)
  done

end


lemma thread_set_cte_wp_at_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. Q (cte_wp_at P p s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. Q (cte_wp_at P p s)\<rbrace>"
  by (auto simp: cte_wp_at_caps_of_state
          intro: thread_set_caps_of_state_trivial [OF x])

lemma (in TcbAcc_AI_arch_tcb_context_set_eq) as_user_inv:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  shows      "\<lbrace>P\<rbrace> as_user t f \<lbrace>\<lambda>x. P\<rbrace>"
  proof -
  have P: "\<And>a b input. (a, b) \<in> fst (f input) \<Longrightarrow> b = input"
    by (rule use_valid [OF _ x], assumption, rule refl)
  have Q: "\<And>s ps. ps (kheap s) = kheap s \<Longrightarrow> kheap_update ps s = s"
    by simp
  show ?thesis
  apply (simp add: as_user_def gets_the_def
                assert_opt_def set_object_def split_def)
  apply wp
  apply (clarsimp dest!: P)
  apply (subst Q, simp_all)
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (case_tac "kheap s t", simp_all)
  apply (case_tac a, simp_all)
  done
qed


lemma det_query_twice:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  assumes y: "det f"
  shows      "do x \<leftarrow> f; y :: tcb \<leftarrow> f; g x y od
               = do x \<leftarrow> f; g x x od"
  apply (subgoal_tac "\<exists>fn. f = (\<lambda>s. ({(fn s, s)}, False))")
   apply clarsimp
   apply (rule bind_cong [OF refl])
   apply (simp add: bind_def)
  apply (rule_tac x="\<lambda>s. fst (THE x. x \<in> fst (f s))" in exI)
  apply (rule ext)
  apply (insert y, simp add: det_def)
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (rule sym)
  apply (rule state_unchanged [OF x])
  apply simp
  done


lemma (in TcbAcc_AI_arch_tcb_context_set_eq) user_getreg_inv[wp]:
  "\<lbrace>P\<rbrace> as_user t (get_register r) \<lbrace>\<lambda>x. P\<rbrace>"
  apply (rule as_user_inv)
  apply (simp add: get_register_def)
  done

lemma as_user_wp_thread_set_helper:
  assumes x: "
         \<lbrace>P\<rbrace> do
                tcb \<leftarrow> gets_the (get_tcb t);
                p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
                thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>) t
         od \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> as_user t m \<lbrace>\<lambda>rv. Q\<rbrace>"
proof -
  have P: "\<And>P Q a b c f.
           \<lbrace>P\<rbrace> do x \<leftarrow> a; y \<leftarrow> b x; z \<leftarrow> c x y; return (f x y z) od \<lbrace>\<lambda>rv. Q\<rbrace>
         = \<lbrace>P\<rbrace> do x \<leftarrow> a; y \<leftarrow> b x; c x y od \<lbrace>\<lambda>rv. Q\<rbrace>"
    apply (simp add: valid_def bind_def return_def split_def)
    done
  have Q: "do
             tcb \<leftarrow> gets_the (get_tcb t);
             p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
             thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>) t
           od
         = do
             tcb \<leftarrow> gets_the (get_tcb t);
             p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
             set_object t (TCB (tcb \<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>))
           od"
    apply (simp add: thread_set_def)
    apply (rule ext)
    apply (rule bind_apply_cong [OF refl])+
    apply (simp add: select_f_def in_monad gets_the_def gets_def)
    apply (clarsimp simp add: get_def bind_def return_def assert_opt_def)
    done
  show ?thesis
    apply (simp add: as_user_def split_def)
    apply (simp add: P x [simplified Q])
    done
qed

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin


end

lemma as_user_psp_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace> as_user t m \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  by (wp as_user_wp_thread_set_helper) simp


lemma as_user_psp_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> as_user t m \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  by (wp as_user_wp_thread_set_helper) simp


context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma as_user_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> as_user a f \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_valid_objs_triv)
  apply (wpsimp simp: tcb_cap_cases_def valid_arch_arch_tcb_context_set)+
  done

end


lemma as_user_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: as_user_def set_object_def split_def)
  apply wp
  apply (clarsimp cong: if_cong)
  apply (clarsimp simp: obj_at_def get_tcb_def valid_idle_def pred_tcb_at_def
                  split: option.splits Structures_A.kernel_object.splits)
  done

lemma as_user_arch[wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> as_user t f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply wp
  apply simp
  done


lemma as_user_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  apply (rule as_user_wp_thread_set_helper)
  apply (wp valid_irq_handlers_lift thread_set_caps_of_state_trivial
                ball_tcb_cap_casesI | simp)+
  done


lemma as_user_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> as_user t f \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>"
  by (wp as_user_wp_thread_set_helper thread_set_iflive_trivial
         ball_tcb_cap_casesI | simp add:)+


lemma as_user_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> as_user t f \<lbrace>\<lambda>_. if_unsafe_then_cap\<rbrace>"
  by (wp as_user_wp_thread_set_helper thread_set_ifunsafe_trivial
         ball_tcb_cap_casesI | simp)+


lemma as_user_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> as_user t f \<lbrace>\<lambda>_. zombies_final\<rbrace>"
  by (wp as_user_wp_thread_set_helper thread_set_zombies_trivial
         ball_tcb_cap_casesI | simp)+


lemma as_user_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     as_user t m
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_refs_trivial | simp)+
  done


lemma as_user_caps [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> as_user a f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def)
  apply wp
  apply (clarsimp cong: if_cong)
  apply (clarsimp simp: get_tcb_def split: option.splits Structures_A.kernel_object.splits)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply simp
  apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def)
  done


crunch it[wp]: as_user "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)

crunch irq_node[wp]: as_user "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)


lemma as_user_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp+

declare thread_set_cur_tcb [wp]

lemma as_user_ct: "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> as_user t m \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def)
  apply wp
  apply simp
  done


lemma as_user_cur [wp]:
  "\<lbrace>cur_tcb\<rbrace> as_user t f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  by (wp as_user_wp_thread_set_helper) simp


lemma as_user_cte_wp_at [wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' c s)\<rbrace> as_user p' f \<lbrace>\<lambda>rv s. P (cte_wp_at P' c s)\<rbrace>"
  by (wp as_user_wp_thread_set_helper
         thread_set_cte_wp_at_trivial
         ball_tcb_cap_casesI | simp)+


lemma as_user_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> as_user t m \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma as_user_pred_tcb_at [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> as_user t' m \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (wp as_user_wp_thread_set_helper thread_set_no_change_tcb_pred
      | simp add: tcb_to_itcb_def)+

lemma ct_in_state_thread_state_lift:
  assumes ct: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  assumes st: "\<And>t. \<lbrace>st_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  shows "\<lbrace>ct_in_state P\<rbrace> f \<lbrace>\<lambda>_. ct_in_state P\<rbrace>"
  apply (clarsimp simp: ct_in_state_def)
  apply (clarsimp simp: valid_def)
  apply (frule (1) use_valid [OF _ ct])
  apply (drule (1) use_valid [OF _ st], assumption)
  done

lemma as_user_ct_in_state:
  "\<lbrace>ct_in_state x\<rbrace> as_user t f \<lbrace>\<lambda>_. ct_in_state x\<rbrace>"
  by (rule ct_in_state_thread_state_lift) (wp as_user_ct)+


lemma set_object_ntfn_at:
  "\<lbrace> ntfn_at p and tcb_at r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. ntfn_at p \<rbrace>"
  apply (rule set_object_at_obj2)
  apply (clarsimp simp: is_obj_defs)
  done

lemma gts_wf[wp]: "\<lbrace>tcb_at t and invs\<rbrace> get_thread_state t \<lbrace>valid_tcb_state\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        valid_objs_def get_tcb_def dom_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (erule allE, erule impE, blast)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  done

lemma idle_thread_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> t = idle_thread s\<rbrace> get_thread_state t \<lbrace>\<lambda>r s. idle r\<rbrace>"
  apply (clarsimp simp: valid_def get_thread_state_def thread_get_def bind_def return_def
                        gets_the_def gets_def get_def assert_opt_def get_tcb_def
                        fail_def valid_idle_def obj_at_def pred_tcb_at_def
                 split: option.splits Structures_A.kernel_object.splits)
  done

lemma set_thread_state_act_valid_objs[wp]:
 "set_thread_state_act t \<lbrace>valid_objs\<rbrace>"
  unfolding set_thread_state_act_def set_scheduler_action_def is_schedulable_def
  by wpsimp

lemma set_thread_state_valid_objs[wp]:
 "\<lbrace>valid_objs and valid_tcb_state st and
   (\<lambda>s. (st_tcb_at (\<lambda>st. \<not> halted st) thread s \<or> halted st \<or> st = Restart))\<rbrace>
  set_thread_state thread st
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp set_object_valid_objs)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                 split: Structures_A.kernel_object.splits option.splits)
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_tcb_def a_type_def tcb_cap_cases_def)
  done

lemma set_bound_notification_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_ntfn ntfn\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma set_tcb_sched_context_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_sc sc\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma set_tcb_yield_to_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_sc sc\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

crunch aligned[wp]: set_thread_state pspace_aligned

lemma set_tcb_obj_ref_aligned[wp]:
 "\<lbrace>pspace_aligned\<rbrace>
  set_tcb_obj_ref f thread ntfn
  \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_aligned)
  apply clarsimp
  done

lemma set_thread_state_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_thread_state st p' \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|clarsimp)+
  apply (clarsimp simp: obj_at_def a_type_def dest!: get_tcb_SomeD)
  done

crunch typ_at[wp]: set_tcb_obj_ref "\<lambda>s. P (typ_at T p s)"


lemma set_thread_state_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> set_thread_state ts t' \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma set_tcb_obj_ref_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> set_tcb_obj_ref f t' ntfn \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma set_thread_state_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_thread_state st p' \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wp hoare_cte_wp_caps_of_state_lift)

lemma set_bound_notification_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_tcb_sched_context_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_tcb_sched_yield_to_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_object_tcb_at [wp]:
  "\<lbrace> tcb_at t' \<rbrace> set_object t (TCB x) \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  by (rule set_object_at_obj1) (simp add: is_tcb)

lemma as_user_tcb [wp]: "\<lbrace>tcb_at t'\<rbrace> as_user t m \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply wp
  apply simp
  done


lemma fold_fun_upd:
  "distinct keys \<Longrightarrow>
   foldl (\<lambda>s (k, v). s(k := v)) s (zip keys vals) key
   = (if key \<in> set (take (length vals) keys)
      then vals ! (the_index keys key)
      else s key)"
  apply (induct keys arbitrary: vals s)
   apply simp
  apply (case_tac vals, simp_all split del: if_split)
  apply (case_tac "key = a", simp_all split del: if_split)
   apply clarsimp
   apply (drule in_set_takeD)
   apply simp
  apply clarsimp
  done

crunch obj_at[wp]: store_word_offs "\<lambda>s. P (obj_at Q p s)"

lemma load_word_offs_P[wp]:
  "\<lbrace>P\<rbrace> load_word_offs a x \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding load_word_offs_def
  by (wp dmo_inv loadWord_inv)

lemma valid_tcb_objs:
  assumes vs: "valid_objs s"
  assumes somet: "get_tcb thread s = Some y"
  shows "valid_tcb thread y s"
proof -
  from somet have inran: "kheap s thread = Some (TCB y)"
    by (clarsimp simp: get_tcb_def
                split: option.splits Structures_A.kernel_object.splits)
  with vs have "valid_obj thread (TCB y) s"
    by (fastforce simp: valid_objs_def dom_def)
  thus ?thesis by (simp add: valid_tcb_def valid_obj_def)
qed


locale TcbAcc_AI_get_cap_valid_ipc =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes get_cap_valid_ipc:
    "\<And>v t.
      \<lbrace>valid_objs and obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_ipc_buffer tcb = v) t\<rbrace>
        get_cap (t, tcb_cnode_index 2)
      \<lbrace>\<lambda>rv (s::'state_ext state). valid_ipc_buffer_cap rv v\<rbrace>"


lemma get_cap_aligned:
  "\<lbrace>valid_objs\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. cap_aligned rv\<rbrace>"
  apply (rule hoare_strengthen_post, rule get_cap_valid)
  apply (clarsimp simp: valid_cap_def)
  done


lemma shiftr_eq_mask_eq:
  "a && ~~ mask b = c && ~~ mask b \<Longrightarrow> a >> b = c >> b"
  apply (rule word_eqI)
  apply (drule_tac x="n + b" in word_eqD)
  apply (case_tac "n + b < size a")
   apply (simp add: nth_shiftr word_size word_ops_nth_size)
  apply (simp add: nth_shiftr)
  apply (auto dest!: test_bit_size simp: word_size)
  done


lemma thread_get_wp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (f tcb) s) ptr s\<rbrace>
    thread_get f ptr
   \<lbrace>P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done


lemma thread_get_sp:
  "\<lbrace>P\<rbrace> thread_get f ptr
   \<lbrace>\<lambda>rv. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> f tcb = rv) ptr and P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done

lemma gbn_wp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (f tcb) s) ptr s \<rbrace>
     get_tcb_obj_ref f ptr
   \<lbrace>P\<rbrace>"
  apply (simp add: get_tcb_obj_ref_def)
  apply (wp thread_get_wp | clarsimp)+
  done

lemmas thread_get_obj_at_eq = thread_get_sp[where P=\<top>, simplified]


lemma wf_cs_0:
  "well_formed_cnode_n sz cn \<Longrightarrow> \<exists>n. n \<in> dom cn \<and> bl_to_bin n = 0"
  unfolding well_formed_cnode_n_def
  apply clarsimp
  apply (rule_tac x = "replicate sz False" in exI)
  apply (simp add: bl_to_bin_rep_False)
  done


lemma ct_active_st_tcb_at_weaken:
  "\<lbrakk> st_tcb_at P (cur_thread s) s;
     \<And>st. P st \<Longrightarrow> active st\<rbrakk>
  \<Longrightarrow> ct_active s"
  apply (unfold ct_in_state_def)
  apply (erule pred_tcb_weakenE)
  apply auto
  done


lemma ct_in_state_decomp:
  assumes x: "\<lbrace>\<lambda>s. t = (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. t = (cur_thread s)\<rbrace>"
  assumes y: "\<lbrace>Pre\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at Prop t\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Pre s \<and> t = (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state Prop\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. t = cur_thread s \<and> st_tcb_at Prop t s"])
   apply (clarsimp simp add: ct_in_state_def)
  apply (rule hoare_vcg_precond_imp)
   apply (wp x y)
  apply simp
  done


(**********************************************************
  !@!@!@!@!@!@!@! UNINTERLEAVE SBA STUFF !@!@!@!@!@!@!@!@!
**********************************************************)

lemma sts_st_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>r. r = ts) t\<rbrace>"
  by (simp add: set_thread_state_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma sbn_bound_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. bound_tcb_at (\<lambda>r. r = ntfn) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma ssc_bound_sc_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. bound_sc_tcb_at (\<lambda>r. r = sc) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma ssc_bound_yt_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. bound_yt_tcb_at (\<lambda>r. r = sc) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma sts_st_tcb_at':
  "\<lbrace>K (P ts)\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule sts_st_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma sbn_bound_tcb_at':
  "\<lbrace>K (P ntfn)\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. bound_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule sbn_bound_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma ssc_bound_tcb_at':
  "\<lbrace>K (P sc)\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule ssc_bound_sc_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma syt_bound_tcb_at':
  "\<lbrace>K (P sc)\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. bound_yt_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule ssc_bound_yt_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

crunch valid_idle[wp]: set_thread_state_act valid_idle

lemma sts_valid_idle [wp]:
  "\<lbrace>valid_idle and
     (\<lambda>s. t = idle_thread s \<longrightarrow> idle ts)\<rbrace>
   set_thread_state t ts
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma sbn_valid_idle [wp]:
  "\<lbrace>valid_idle and
     (\<lambda>s. t = idle_thread s \<longrightarrow> \<not> bound ntfn)\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma ssc_valid_idle [wp]:
  "\<lbrace>valid_idle and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wp
  apply (clarsimp cong: if_cong
                  simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma syt_valid_idle [wp]:
  "\<lbrace>valid_idle and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wp
  apply (clarsimp cong: if_cong
                  simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunches set_thread_state, set_tcb_obj_ref
  for distinct[wp]: pspace_distinct

lemma cur_tcb_scheduler_action[simp]:
  "cur_tcb (scheduler_action_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

crunch cur_tcb[wp]: set_thread_state_act cur_tcb

lemma sts_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. cur_tcb s\<rbrace>"
  unfolding set_thread_state_def set_object_def
  apply wpsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  done

lemma sbn_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_tcb_obj_ref f t ntfn \<lbrace>\<lambda>rv s. cur_tcb s\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def set_object_def gets_the_def
                        valid_def in_monad)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  done

crunch iflive[wp]: set_thread_state_act if_live_then_nonz_cap

lemma sts_iflive[wp]:
  "\<lbrace>\<lambda>s. (\<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply wpsimp
  by (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                simp: tcb_cap_cases_def live_def
                split: Structures_A.thread_state.splits)

lemma sbn_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound ntfn \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply wpsimp
  apply (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: thread_state.splits)
  done

lemma ssc_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound sc \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply wpsimp
  apply_trace (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: Structures_A.thread_state.splits)
  done

lemma syt_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound sc \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply wpsimp
  apply (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: Structures_A.thread_state.splits)
  done

crunch ifunsafe[wp]: set_thread_state_act if_unsafe_then_cap

lemma sts_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp|simp)+
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma sbn_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma ssc_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma syt_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

crunch zombies[wp]: set_thread_state zombies_final
  (simp: tcb_cap_cases_def)

lemma sbn_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_bound_notification_update f ntfn \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma ssc_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_sched_context_update f sc \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma syt_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_yield_to_update f sc \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma sts_refs_of_helper: "
          {r. (r \<in> tcb_st_refs_of ts \<or>
               r \<in> get_refs TCBBound ntfnptr \<or>
               r \<in> get_refs TCBSchedContext sc \<or>
               r \<in> get_refs TCBYieldTo yt) \<and>
              (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)} =
          get_refs TCBBound ntfnptr \<union>
          get_refs TCBSchedContext sc \<union>
          get_refs TCBYieldTo yt"
  by (auto simp: tcb_st_refs_of_def get_refs_def
          split: thread_state.splits option.splits)

declare scheduler_action_update.state_refs_update[simp]

crunches set_thread_state_act
  for refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"

lemma sts_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (t := tcb_st_refs_of st
                         \<union> {r. r \<in> state_refs_of s t \<and>
                 (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}))\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                   simp: state_refs_of_def
                 intro!: ext)
  apply (simp add: get_tcb_def sts_refs_of_helper)
  apply auto
  done

lemma kheap_Some_state_hyp_refs_ofD:
  "kheap s p = Some ko \<Longrightarrow> state_hyp_refs_of s p = hyp_refs_of ko"
  by (rule ko_at_state_hyp_refs_ofD; simp add: obj_at_def)

lemma sts_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp | simp del: fun_upd_apply)+
  apply (clarsimp simp: get_tcb_def split: option.splits kernel_object.splits
                  simp del: fun_upd_apply)
  apply (subst state_hyp_refs_of_tcb_state_update; assumption)
  done

lemma sbn_refs_of_helper:
          "{r. (r \<in> tcb_st_refs_of ts \<or>
               r \<in> get_refs TCBBound ntfnptr) \<and>
              snd r \<noteq> TCBBound} =
          tcb_st_refs_of ts"
  by (auto simp add: tcb_st_refs_of_def get_refs_def split: thread_state.splits option.splits)

lemma sbn_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case ntfn of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBBound)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBBound}))))\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                 simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def get_tcb_rev
               intro!: ext split: option.splits if_splits thread_state.split)

lemma sbn_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_bound_ntfn_update; auto simp: get_tcb_def)
  done

lemma ssc_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBSchedContext)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBSchedContext}))))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
         simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def get_tcb_rev
         intro!: ext split: option.splits if_splits thread_state.split)

lemma ssc_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_sched_context_update; auto simp: get_tcb_def)
  done

lemma syt_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBYieldTo)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBYieldTo}))))\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def set_object_def)
  by (fastforce elim!: rsubst[where P=P] dest!: get_tcb_SomeD
         simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def get_tcb_rev
         intro!: ext split: option.splits if_splits thread_state.split)

lemma syt_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_yield_to_update; auto simp: get_tcb_def)
  done

lemma set_thread_state_thread_set:
  "set_thread_state p st = (do thread_set (tcb_state_update (\<lambda>_. st)) p;
                               set_thread_state_act p
                            od)"
  by (simp add: set_thread_state_def thread_set_def bind_assoc)

lemma set_tcb_obj_ref_thread_set:
  "set_tcb_obj_ref f p sc = thread_set (f (\<lambda>_. sc)) p"
  by (simp add: set_tcb_obj_ref_def thread_set_def bind_assoc)

crunch pred_tcb_at[wp]: set_thread_state_act "pred_tcb_at proj P t"

lemma sts_st_tcb_at_neq:
  "\<lbrace>pred_tcb_at proj P t and K (t\<noteq>t')\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (simp add: pred_tcb_at_def obj_at_def)
  done

lemma sbn_st_tcb_at_neq:
  "\<lbrace>pred_tcb_at proj P t and K (t\<noteq>t')\<rbrace> set_tcb_obj_ref f t' new \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (simp add: pred_tcb_at_def obj_at_def)
  done


lemma sts_st_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P ts) \<and> ((t \<noteq> t') \<longrightarrow> st_tcb_at P t' s)\<rbrace>
     set_thread_state t ts
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp sts_st_tcb_at')
   apply simp
  apply (wp sts_st_tcb_at_neq)
  apply simp
  done

lemma sbn_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P ntfn) \<and> ((t \<noteq> t') \<longrightarrow> bound_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv. bound_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp sbn_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma ssc_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P sc) \<and> ((t \<noteq> t') \<longrightarrow> bound_sc_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp ssc_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma syt_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P sc) \<and> ((t \<noteq> t') \<longrightarrow> bound_yt_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv. bound_yt_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp syt_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma sbn_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_bound_notification_update tcb ntfn \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wp
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma ssc_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wp
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma syt_st_tcb_at[wp]:
  "\<lbrace>st_tcb_at P t\<rbrace> set_tcb_obj_ref tcb_yield_to_update tcb ntfn \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply wp
  apply (auto simp: pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunches set_thread_state
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and ioc[wp]: "\<lambda>s. P (is_original_cap s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"

lemma set_thread_state_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_thread_state p st \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (rule valid_mdb_lift; wp)

lemma set_bound_notification_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_tcb_sched_cotnext_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_sched_context_update p sc \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_tcb_yield_to_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_yield_to_update p sc \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_thread_state_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_thread_state p st \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wp)

lemma set_bound_notification_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

lemma set_tcb_sched_context_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

lemma set_tcb_yield_to_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

crunch arch [wp]: set_thread_state, set_tcb_obj_ref  "\<lambda>s. P (arch_state s)"


lemma st_tcb_ex_cap:
  "\<lbrakk> st_tcb_at P t s; if_live_then_nonz_cap s;
      \<And>st. P st \<Longrightarrow> \<not> halted st\<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  unfolding pred_tcb_at_def
  by (erule (1) if_live_then_nonz_capD, fastforce simp: live_def)

lemma bound_tcb_ex_cap:
  "\<lbrakk> bound_tcb_at P t s; if_live_then_nonz_cap s;
      \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  unfolding pred_tcb_at_def
  by (erule (1) if_live_then_nonz_capD, fastforce simp: live_def)

locale TcbAcc_AI_pred_tcb_cap_wp_at =
  fixes proj :: "itcb \<Rightarrow> 'proj"
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes pred_tcb_cap_wp_at:
    "\<And>P t (s::'state_ext state) ref Q.
      \<lbrakk> pred_tcb_at proj P t s; valid_objs s;
        ref \<in> dom tcb_cap_cases;
        \<forall>cap. (pred_tcb_at proj P t s \<and> tcb_cap_valid cap (t, ref) s) \<longrightarrow> Q cap\<rbrakk>
      \<Longrightarrow> cte_wp_at Q (t, ref) s"


locale TcbAcc_AI_st_tcb_at_cap_wp_at = TcbAcc_AI_pred_tcb_cap_wp_at itcb_state state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself"


context TcbAcc_AI_st_tcb_at_cap_wp_at begin

lemma dom_tcb_cap_cases:
  "tcb_cnode_index 0 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 1 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 2 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 3 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 4 \<in> dom tcb_cap_cases"
  by clarsimp+

end

lemma set_thread_state_interrupt_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  set_thread_state param_a param_b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  apply (simp add: set_thread_state_def)
  apply (wp|simp add: set_object_def)+
  done
(*crunch irq_node[wp]: set_thread_state "\<lambda>s. P (interrupt_irq_node s)"*)

crunch irq_node[wp]: set_tcb_obj_ref "\<lambda>s. P (interrupt_irq_node s)"

crunch interrupt_states[wp]: set_tcb_obj_ref, set_thread_state "\<lambda>s. P (interrupt_states s)"

lemmas set_thread_state_caps_of_state = sts_caps_of_state

lemmas set_thread_state_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_thread_state_caps_of_state
                                  set_thread_state_interrupt_states]

lemmas set_bound_notification_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_bound_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]

lemmas set_tcb_sched_context_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_tcb_sc_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]

lemmas set_tcb_yield_to_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_tcb_yt_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]


lemma sts_obj_at_impossible:
  "(\<And>tcb. \<not> P (TCB tcb)) \<Longrightarrow> \<lbrace>obj_at P p\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: thread_set_obj_at_impossible
              simp: set_object_def obj_at_def get_tcb_def split: kernel_object.splits)

lemma sbn_obj_at_impossible:
  "(\<And>tcb. \<not> P (TCB tcb)) \<Longrightarrow> \<lbrace>obj_at P p\<rbrace> set_tcb_obj_ref f t ntfn \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  unfolding set_tcb_obj_ref_thread_set
  by (wp thread_set_obj_at_impossible, simp)

crunch only_idle[wp]: set_thread_state_act only_idle

lemma sts_only_idle:
  "\<lbrace>only_idle and (\<lambda>s. idle st \<longrightarrow> t = idle_thread s)\<rbrace>
  set_thread_state t st \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)
  done

lemma sbn_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace>
  set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma ssc_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace>
  set_tcb_obj_ref tcb_sched_context_update t ntfn \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma syt_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace>
  set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma set_thread_state_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace>
      set_thread_state p st \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (rule pspace_in_kernel_window_atyp_lift)
   apply wp+
  done

crunches set_thread_state
  for pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  (wp: set_object_pspace_respects_device_region simp: tcb_cap_cases_def)

lemma set_tcb_obj_ref_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace>
      set_tcb_obj_ref f p ntfn \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set, wp)

crunch pspace_respects_device_region[wp]: set_tcb_obj_ref pspace_respects_device_region
  (wp: set_object_pspace_respects_device_region)

lemma set_bound_nofitication_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_tcb_sched_context_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_tcb_yield_to_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_bound_notification_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma set_tcb_sched_context_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma set_tcb_yield_to_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma valid_ioc_sched_act_update[simp]:
  "valid_ioc (scheduler_action_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

crunch valid_ioc[wp]: set_thread_state_act valid_ioc

lemma set_thread_state_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_valid_ioc_caps)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma set_bound_notification_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma set_tcb_sched_context_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_sched_context_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma set_tcb_yield_to_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma sts_invs_minor:
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st) t
     and (\<lambda>s. \<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
     and (\<lambda>s. t \<noteq> idle_thread s)
     and (\<lambda>s. st_tcb_at (\<lambda>st. \<not> halted st) t s \<or> halted st \<or> st = Restart)
     and (\<lambda>s. \<forall>typ. (idle_thread s, typ) \<notin> tcb_st_refs_of st)
     and K (\<not>idle st)
     and invs\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wp valid_irq_node_typ sts_only_idle)
  apply clarsimp
  apply (rule conjI, simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def doubleton_eq_iff
                  split: thread_state.splits if_split_asm)
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: st_tcb_at_state_refs_ofD)
  apply (auto simp: get_refs_def split: option.splits)
  done

lemma sts_invs_minor2:
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st \<and> \<not> awaiting_reply st') t
     and invs and ex_nonz_cap_to t and (\<lambda>s. t \<noteq> idle_thread s)
     and K (\<not> awaiting_reply st \<and> \<not>idle st)
     and (\<lambda>s. st_tcb_at (\<lambda>st. \<not> halted st) t s \<or> halted st \<or> st = Restart)\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle)
  apply clarsimp
  apply (rule conjI, simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def doubleton_eq_iff
                  split: thread_state.splits if_split_asm)
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: st_tcb_at_state_refs_ofD)
  apply (auto simp: get_refs_def split: option.splits)
  done

lemma sbn_invs_minor:
  "\<lbrace>bound_tcb_at (\<lambda>ntfn'. get_refs TCBBound ntfn' = get_refs TCBBound ntfn) t
    and (\<lambda>s. bound ntfn \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle)
  apply clarsimp
  apply (simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma ssc_invs_minor:
  "\<lbrace>bound_sc_tcb_at (\<lambda>sc'. get_refs TCBSchedContext sc' = get_refs TCBSchedContext sc) t
    and (\<lambda>s. bound sc \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ)
  apply (clarsimp simp: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma syt_invs_minor:
  "\<lbrace>bound_yt_tcb_at (\<lambda>sc'. get_refs TCBYieldTo sc' = get_refs TCBYieldTo sc) t
    and (\<lambda>s. bound sc \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ)
  apply (clarsimp simp: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma thread_set_valid_cap:
  shows "\<lbrace>valid_cap c\<rbrace> thread_set t p \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma thread_set_cte_at:
  shows "\<lbrace>cte_at c\<rbrace> thread_set t p \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  by (wp valid_cte_at_typ)


lemma set_thread_state_ko:
  "\<lbrace>ko_at obj ptr and K (\<not>is_tcb obj)\<rbrace> set_thread_state x st \<lbrace>\<lambda>rv. ko_at obj ptr\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp set_object_ko|clarsimp)+
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemma set_tcb_obj_ref_ko:
  "\<lbrace>ko_at obj ptr and K (\<not>is_tcb obj)\<rbrace> set_tcb_obj_ref f x ntfn \<lbrace>\<lambda>rv. ko_at obj ptr\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_ko, clarsimp)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemmas set_thread_state_valid_cap = set_thread_state_typ_ats(17)

crunch valid_cap: set_tcb_obj_ref "valid_cap c"

crunch cte_at: set_tcb_obj_ref "cte_at p"


lemma as_user_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> as_user f t \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (rule valid_mdb_lift)
    prefer 2
    apply wp
    apply simp
   prefer 2
   apply (simp add: set_object_def)
   apply wpsimp
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (simp add: cte_wp_at_cases)
  apply (drule get_tcb_SomeD)
  apply (auto simp: tcb_cap_cases_def)
  done


lemma dom_mapM:
  assumes "\<And>x. empty_fail (m x)"
  shows "do_machine_op (mapM m xs) = mapM (do_machine_op \<circ> m) xs"
  by (rule submonad_mapM [OF submonad_do_machine_op submonad_do_machine_op,
                             simplified]) fact+


lemma sts_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma set_tcb_obj_ref_ex_nonz_cap_to[wp]:
  "\<lbrace>(\<lambda>s. ex_nonz_cap_to p s
      \<and> obj_at (same_caps (TCB (f (\<lambda>y. new) (the (get_tcb p s))))) p s)\<rbrace>
   set_tcb_obj_ref f p new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def ex_cap_to_after_update)

lemma set_bound_notification_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma ct_in_state_sched_act_update[simp]:
  "ct_in_state P (scheduler_action_update f s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

crunch ct_in_state[wp]: set_thread_state_act "ct_in_state P"

lemma ct_in_state_set:
  "P st \<Longrightarrow> \<lbrace>\<lambda>s. cur_thread s = t\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. ct_in_state P \<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  by (wp|simp add: ct_in_state_def pred_tcb_at_def obj_at_def)+


lemma sts_ctis_neq:
  "\<lbrace>\<lambda>s. cur_thread s \<noteq> t \<and> ct_in_state P s\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. ct_in_state P\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp add: pred_tcb_at_def obj_at_def ct_in_state_def)+
  done

lemma valid_running [simp]:
  "valid_tcb_state Structures_A.Running = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)


lemma valid_inactive [simp]:
  "valid_tcb_state Structures_A.Inactive = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)

lemma ntfn_queued_st_tcb_at:
  "\<And>P. \<lbrakk>ko_at (Notification ep) ptr s; (t, rt) \<in> ntfn_q_refs_of (ntfn_obj ep);
         valid_objs s; sym_refs (state_refs_of s);
         \<And>ref. P (Structures_A.BlockedOnNotification ref) \<rbrakk>
   \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac "ntfn_obj ep", simp_all)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp)
  apply (erule_tac y="(t,NTFNSignal)" in my_BallE)
   apply (clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

lemma ep_queued_st_tcb_at:
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>ref pl r. P (Structures_A.BlockedOnSend ref pl) \<and>
  P (Structures_A.BlockedOnReceive ref r) \<rbrakk>
    \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done


lemma thread_set_ct_running:
  "(\<And>tcb. tcb_state (f tcb) = tcb_state tcb) \<Longrightarrow>
  \<lbrace>ct_running\<rbrace> thread_set f t \<lbrace>\<lambda>rv. ct_running\<rbrace>"
  apply (simp add: ct_in_state_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
   apply (wp thread_set_no_change_tcb_state; simp)
  apply (simp add: thread_set_def set_object_def)
  apply wp
  apply simp
  done


lemmas thread_set_caps_of_state_trivial2
  = thread_set_caps_of_state_trivial [OF ball_tcb_cap_casesI]

lemmas sts_typ_ats = abs_typ_at_lifts [OF set_thread_state_typ_at]


lemma sts_tcb_ko_at:
  "\<lbrace>\<lambda>s. \<forall>v'. v = (if t = t' then v' \<lparr>tcb_state := ts\<rparr> else v')
              \<longrightarrow> ko_at (TCB v') t' s \<longrightarrow> P v\<rbrace>
      set_thread_state t ts
   \<lbrace>\<lambda>rv s. ko_at (TCB v) t' s \<longrightarrow> P v\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  apply (simp add: get_tcb_def)
  done


lemma sts_tcb_cap_valid_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> (case tcb_cap_cases ref of
                         None \<Rightarrow> True
                       | Some (getF, setF, restr) \<Rightarrow> restr t ts cap)
                   \<and> (ref = tcb_cnode_index 2 \<longrightarrow>
                        (\<forall>tcb. ko_at (TCB tcb) t' s \<longrightarrow>
                             valid_ipc_buffer_cap cap (tcb_ipc_buffer tcb)))) \<and>
        (t \<noteq> t' \<longrightarrow> tcb_cap_valid cap (t', ref) s)\<rbrace>
   set_thread_state t ts
   \<lbrace>\<lambda>_ s. tcb_cap_valid cap (t', ref) s\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: tcb_cap_valid_def tcb_at_typ)
   apply (subst imp_conv_disj)
   apply (wp hoare_vcg_disj_lift sts_st_tcb_at_cases
             hoare_vcg_const_imp_lift sts_tcb_ko_at
             hoare_vcg_all_lift)
  apply (clarsimp simp: tcb_at_typ tcb_cap_valid_def split: option.split)
  done


lemmas set_mrs_redux =
   set_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

locale TcbAcc_AI_arch_tcb_context_get_eq =
    assumes arch_tcb_context_get_eq[simp]:
      "\<And> t uc. arch_tcb_context_get (arch_tcb_context_set uc t) = uc"

locale TcbAcc_AI
  = TcbAcc_AI_storeWord_invs state_ext_t
  + TcbAcc_AI_valid_ipc_buffer_cap_0 state_ext_t
  + TcbAcc_AI_get_cap_valid_ipc state_ext_t
  + TcbAcc_AI_st_tcb_at_cap_wp_at state_ext_t
  + TcbAcc_AI_arch_tcb_context_set_eq
  + TcbAcc_AI_arch_tcb_context_get_eq
  for state_ext_t :: "'state_ext::state_ext itself"


context TcbAcc_AI begin

lemma as_user_invs[wp]: "\<lbrace>invs:: 'state_ext state \<Rightarrow> bool\<rbrace> as_user t m \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule as_user_wp_thread_set_helper)
  apply (rule hoare_pre)
  apply (wp thread_set_invs_trivial ball_tcb_cap_casesI | simp)+
  done

lemma set_mrs_invs[wp]:
  "\<And>receiver recv_buf mrs.
    \<lbrace> invs and tcb_at receiver :: 'state_ext state \<Rightarrow> bool \<rbrace>
      set_mrs receiver recv_buf mrs
    \<lbrace>\<lambda>rv. invs \<rbrace>"
  by (wpsimp wp: mapM_wp' storeWord_invs thread_set_invs_trivial hoare_vcg_imp_lift
           simp: set_mrs_redux zipWithM_x_mapM store_word_offs_def tcb_cap_cases_def
      split_del: if_split)

end


lemma set_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>P\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch :=arch_tcb_context_set (c tcb) (tcb_arch tcb)\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: set_mrs_redux)
  apply (case_tac t)
   apply simp
   apply (wp ts)
  apply (simp add: zipWithM_x_mapM store_word_offs_def split_def
              split del: if_split)
  apply (wp mapM_wp dmo)
     apply simp
    apply blast
   apply (rule ts)
  apply assumption
  done

lemma set_mrs_st_tcb [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_mrs r t' mrs \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (rule thread_set_no_change_tcb_pred)
   apply (simp add: tcb_to_itcb_def)
  apply wp
  done

lemma get_tcb_ko_atD:
  "get_tcb t s = Some tcb \<Longrightarrow> ko_at (TCB tcb) t s"
  by auto

lemma live_tcb_domain_update[simp]:
  "live (TCB (tcb_domain_update f t)) = live (TCB t)"
  by (simp add: live_def)

lemma live_tcb_priority_update[simp]:
  "live (TCB (tcb_priority_update f t)) = live (TCB t)"
  by (simp add: live_def)

crunches thread_set_domain, thread_set_priority
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and valid_irq_states[wp]: valid_irq_states
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and only_idle[wp]: only_idle
  and valid_arch_state[wp]: valid_arch_state
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_machine_state[wp]: valid_machine_state
  and valid_asid_map[wp]: valid_asid_map
  and global_refs[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps tcb_cap_cases_def)

lemmas thread_set_domain_typ_ats[wp] = abs_typ_at_lifts[OF thread_set_domain_typ_at]
lemmas thread_set_priority_typ_ats[wp] = abs_typ_at_lifts[OF thread_set_priority_typ_at]

lemma thread_set_domain_caps_of_state[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_def
  apply wpsimp
  apply (erule rsubst[of P])
  apply (rule cte_wp_caps_of_lift)
  apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_cte_wp_at[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (cte_wp_at Q p s)\<rbrace>"
  by (wpsimp simp: cte_wp_at_caps_of_state)

lemma thread_set_domain_valid_objs[wp]:
  "thread_set_domain t d \<lbrace>valid_objs\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_valid_objs)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule (1) bspec)
  by (auto simp: tcb_cap_cases_def)

lemma thread_set_domain_if_live_then_nonz_cap[wp]:
  "thread_set_domain t d \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply wpsimp
  apply (auto simp: if_live_then_nonz_cap_def obj_at_def tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_zombies_final[wp]:
  "thread_set_domain t d \<lbrace>zombies_final\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def)

lemma thread_set_domain_refs_of[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_is_modify
  apply (wpsimp simp: state_refs_of_def)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply (clarsimp split: option.splits dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_hyp_refs_of[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_def
  supply fun_upd_apply [simp del]
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  apply (subst state_hyp_refs_of_tcb_domain_update; auto simp: get_tcb_def)
  done


lemma thread_set_domain_valid_idle[wp]:
  "thread_set_domain t d \<lbrace>valid_idle\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply wpsimp
  apply (drule get_tcb_SomeD)
  apply (rule conjI, fastforce simp: obj_at_def)
  apply clarsimp
  apply (rule conjI, rule refl)
  apply (rule conjI, rule refl)
  apply simp
  done

lemma thread_set_domain_if_unsafe_then_cap[wp]:
  "thread_set_domain t d \<lbrace>if_unsafe_then_cap\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def)

lemma thread_set_domain_valid_irq_node[wp]:
  "thread_set_domain t d \<lbrace>valid_irq_node\<rbrace>"
  apply (wpsimp simp: valid_irq_node_def wp: hoare_vcg_all_lift)
   apply (rule hoare_lift_Pf[where f="interrupt_irq_node"]; wp)
  apply simp
  done

lemma thread_set_domain_valid_irq_handlers[wp]:
  "thread_set_domain t d \<lbrace>valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_lift_Pf[where f="caps_of_state"]; wp)
  done

lemma thread_set_domain_valid_arch_caps[wp]:
  "thread_set_domain t d \<lbrace>valid_arch_caps\<rbrace>"
  unfolding thread_set_domain_def
  by (wpsimp wp: thread_set_arch_caps_trivial simp: tcb_cap_cases_def)

lemma thread_set_domain_invs[wp]:
  "thread_set_domain t d \<lbrace>invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_mdb_lift hoare_vcg_all_lift hoare_vcg_imp_lift
           simp: valid_ioc_def valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)



lemma thread_set_priority_caps_of_state[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_def
  apply wpsimp
  apply (erule rsubst[of P])
  apply (rule cte_wp_caps_of_lift)
  apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_cte_wp_at[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (cte_wp_at Q p s)\<rbrace>"
  by (wpsimp simp: cte_wp_at_caps_of_state)

lemma thread_set_priority_valid_objs[wp]:
  "thread_set_priority t d \<lbrace>valid_objs\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_valid_objs)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule (1) bspec)
  by (auto simp: tcb_cap_cases_def)

lemma thread_set_priority_if_live_then_nonz_cap[wp]:
  "thread_set_priority t d \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply wpsimp
  apply (auto simp: if_live_then_nonz_cap_def obj_at_def tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_zombies_final[wp]:
  "thread_set_priority t d \<lbrace>zombies_final\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def)

lemma thread_set_priority_refs_of[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_is_modify
  apply (wpsimp simp: state_refs_of_def)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply (clarsimp split: option.splits dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_hyp_refs_of[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_def
  supply fun_upd_apply [simp del]
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  apply (subst state_hyp_refs_of_tcb_priority_update; auto simp: get_tcb_def)
  done


lemma thread_set_priority_valid_idle[wp]:
  "thread_set_priority t d \<lbrace>valid_idle\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply wpsimp
  apply (drule get_tcb_SomeD)
  apply (rule conjI, fastforce simp: obj_at_def)
  apply clarsimp
  apply (rule conjI, rule refl)
  apply (rule conjI, rule refl)
  apply simp
  done

lemma thread_set_priority_if_unsafe_then_cap[wp]:
  "thread_set_priority t d \<lbrace>if_unsafe_then_cap\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def)

lemma thread_set_priority_valid_irq_node[wp]:
  "thread_set_priority t d \<lbrace>valid_irq_node\<rbrace>"
  apply (wpsimp simp: valid_irq_node_def wp: hoare_vcg_all_lift)
   apply (rule hoare_lift_Pf[where f="interrupt_irq_node"]; wp)
  apply simp
  done

lemma thread_set_priority_valid_irq_handlers[wp]:
  "thread_set_priority t d \<lbrace>valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_lift_Pf[where f="caps_of_state"]; wp)
  done

lemma thread_set_priority_valid_arch_caps[wp]:
  "thread_set_priority t d \<lbrace>valid_arch_caps\<rbrace>"
  unfolding thread_set_priority_def
  by (wpsimp wp: thread_set_arch_caps_trivial simp: tcb_cap_cases_def)

lemma thread_set_priority_invs[wp]:
  "thread_set_priority t d \<lbrace>invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_mdb_lift hoare_vcg_all_lift hoare_vcg_imp_lift
           simp: valid_ioc_def valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)

end
