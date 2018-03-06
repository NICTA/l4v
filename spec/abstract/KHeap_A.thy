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
Functions to access kernel memory.
*)

chapter {* Accessing the Kernel Heap *}

theory KHeap_A
imports Exceptions_A
begin

text {* This theory gives auxiliary getter and setter methods
for kernel objects. *}

section "General Object Access"

definition
  get_object :: "obj_ref \<Rightarrow> (kernel_object,'z::state_ext) s_monad"
where
  "get_object ptr \<equiv> do
     kh \<leftarrow> gets kheap;
     assert (kh ptr \<noteq> None);
     return $ the $ kh ptr
   od"

definition
  set_object :: "obj_ref \<Rightarrow> kernel_object \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_object ptr obj \<equiv> do
     s \<leftarrow> get;
     kh \<leftarrow> return $ (kheap s)(ptr := Some obj);
     put (s \<lparr> kheap := kh \<rparr>)
   od"


section "TCBs"

definition
  thread_get :: "(tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "thread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     return $ f tcb
   od"

definition
  thread_set :: "(tcb \<Rightarrow> tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "thread_set f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     set_object tptr $ TCB $ f tcb
   od"

definition
  arch_thread_get :: "(arch_tcb \<Rightarrow> 'a) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "arch_thread_get f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     return $ f (tcb_arch tcb)
   od"

definition
  arch_thread_set :: "(arch_tcb \<Rightarrow> arch_tcb) \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "arch_thread_set f tptr \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     set_object tptr $ TCB $ tcb \<lparr> tcb_arch := f (tcb_arch tcb) \<rparr>
   od"

definition
  get_thread_state :: "obj_ref \<Rightarrow> (thread_state,'z::state_ext) s_monad"
where
  "get_thread_state ref \<equiv> thread_get tcb_state ref"

definition
  get_bound_notification :: "obj_ref \<Rightarrow> (obj_ref option,'z::state_ext) s_monad"
where
  "get_bound_notification ref \<equiv> thread_get tcb_bound_notification ref"

definition
  set_bound_notification :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "set_bound_notification ref ntfn \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_bound_notification := ntfn \<rparr>))
   od"

section {* Scheduling Contexts *}

definition
  get_sched_context :: "obj_ref \<Rightarrow> (sched_context,'z::state_ext) s_monad"
where
  "get_sched_context ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     case kobj of SchedContext sc \<Rightarrow> return sc
                 | _ \<Rightarrow> fail
   od"

definition
  set_sched_context :: "obj_ref \<Rightarrow> sched_context \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_sched_context ptr sc \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (case obj of SchedContext sc \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (SchedContext sc)
   od"



(****)

definition
  is_schedulable :: "obj_ref \<Rightarrow> bool \<Rightarrow> ('z::state_ext state, bool) nondet_monad"
where
  "is_schedulable tcb_ptr in_release_q \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tcb_ptr;
    if Option.is_none (tcb_sched_context tcb)
    then return False
    else do
      sc \<leftarrow> get_sched_context $ the $ tcb_sched_context tcb;
      return (runnable (tcb_state tcb)
              \<and> sc_refill_max sc > 0 \<and> \<not>in_release_q)
    od
  od"

definition
  is_schedulable_opt :: "obj_ref \<Rightarrow> bool \<Rightarrow> 'z::state_ext state \<Rightarrow> bool option"
where 
  "is_schedulable_opt tcb_ptr in_release_q \<equiv> \<lambda>s.
    case get_tcb tcb_ptr s of None \<Rightarrow> None | Some tcb \<Rightarrow>
      (case tcb_sched_context tcb of None => Some False
       | Some sc_ptr => 
           Some (runnable (tcb_state tcb)   (* FIXME *)
           \<and> \<not>in_release_q))"

definition reschedule_required :: "unit det_ext_monad" where
  "reschedule_required \<equiv> do
     action \<leftarrow> gets scheduler_action;
     case action of 
       switch_thread t \<Rightarrow> do
         in_release_q \<leftarrow> gets $ in_release_queue t;
         sched \<leftarrow> is_schedulable t in_release_q;
         when sched $ tcb_sched_action (tcb_sched_enqueue) t
       od
     | _ \<Rightarrow> return ();
     set_scheduler_action choose_new_thread;
     modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>)
   od"

definition
  schedule_tcb :: "obj_ref \<Rightarrow> unit det_ext_monad"
where
  "schedule_tcb tcb_ptr \<equiv> do
    cur \<leftarrow> gets cur_thread;
    sched_act \<leftarrow> gets scheduler_action;
    in_release_q \<leftarrow> gets $ in_release_queue tcb_ptr;
    schedulable \<leftarrow> is_schedulable tcb_ptr in_release_q;
    when (tcb_ptr = cur \<and> sched_act = resume_cur_thread \<and> \<not>schedulable) $ reschedule_required
  od"



(***)

definition
  set_thread_state :: "obj_ref \<Rightarrow> thread_state \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_thread_state ref ts \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb ref;
     set_object ref (TCB (tcb \<lparr> tcb_state := ts \<rparr>));
     do_extended_op (schedule_tcb ref)
   od"

definition
  set_mcpriority :: "obj_ref \<Rightarrow> priority \<Rightarrow> (unit, 'z::state_ext) s_monad"  where
  "set_mcpriority ref mcp \<equiv> thread_set (\<lambda>tcb. tcb\<lparr>tcb_mcpriority:=mcp\<rparr>) ref "

section {* Synchronous and Asyncronous Endpoints *}

section "simple kernel objects"
(* to be used for abstraction unifying kernel objects other than TCB and CNode *)

definition
  partial_inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a option)"
where
  "partial_inv f x = (if \<exists>!y. f y = x then Some (THE y. f y = x) else None)"

lemma proj_inj: "inj f \<Longrightarrow> (partial_inv f ko = Some v) = (f v = ko)"
  by (auto simp: partial_inv_def the_equality injD)

lemma inj_Endpoint: "inj Endpoint" by (auto intro: injI)
lemma inj_Notification: "inj Notification"  by (auto intro: injI)

lemmas proj_inj_ep[simp] = proj_inj[OF inj_Endpoint]
lemma proj_ko_type_ep[simp]: "(\<exists>v. partial_inv Endpoint  ko = Some (v::endpoint)) = (a_type ko = AEndpoint)"
  by (cases ko; auto simp: partial_inv_def a_type_def)

lemmas proj_inj_ntfn[simp] = proj_inj[OF inj_Notification]
lemma proj_ko_type_ntfn[simp]:
  "(\<exists>v. partial_inv Notification  ko = Some (v::notification)) = (a_type ko = ANTFN)"
  by (cases ko; auto simp: partial_inv_def a_type_def)


abbreviation
  "is_simple_type \<equiv> (\<lambda>ob. a_type ob \<in> {AEndpoint, ANTFN})"


definition
  get_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "get_simple_ko f ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     assert (is_simple_type kobj);
     (case partial_inv f kobj of Some e \<Rightarrow> return e | _ \<Rightarrow> fail)
   od"


definition
  set_simple_ko :: "('a \<Rightarrow> kernel_object) \<Rightarrow> obj_ref \<Rightarrow> 'a \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_simple_ko f ptr ep \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (is_simple_type obj);
     assert (case partial_inv f obj of Some e \<Rightarrow> a_type obj = a_type (f ep) | _ \<Rightarrow> False);
     set_object ptr (f ep)
   od"

section {* Reply Objects *}

definition
  get_reply :: "obj_ref \<Rightarrow> reply det_ext_monad"
where
  "get_reply ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of Reply r \<Rightarrow> return r
                 | _ \<Rightarrow> fail)
   od"
  
definition
  set_reply :: "obj_ref \<Rightarrow> reply \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_reply ptr r \<equiv> do
     obj \<leftarrow> get_object ptr;
     assert (case obj of Reply _ \<Rightarrow> True | _ \<Rightarrow> False);
     set_object ptr (Reply r)
   od"

abbreviation
  "get_reply_caller r \<equiv> liftM reply_caller (get_reply r)"


section {* IRQ State and Slot *}

definition
  get_irq_state :: "irq \<Rightarrow> (irq_state,'z::state_ext) s_monad" where
 "get_irq_state irq \<equiv> gets (\<lambda>s. interrupt_states s irq)"

definition
  set_irq_state :: "irq_state \<Rightarrow> irq \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_irq_state state irq \<equiv> do
    modify (\<lambda>s. s \<lparr> interrupt_states := (interrupt_states s) (irq := state)\<rparr>);
    do_machine_op $ maskInterrupt (state = IRQInactive) irq
  od"

definition
  get_irq_slot :: "irq \<Rightarrow> (cslot_ptr,'z::state_ext) s_monad" where
 "get_irq_slot irq \<equiv> gets (\<lambda>st. (interrupt_irq_node st irq, []))"


section "User Context"

text {*
  Changes user context of specified thread by running
  specified user monad.
*}
definition
  as_user :: "obj_ref \<Rightarrow> 'a user_monad \<Rightarrow> ('a,'z::state_ext) s_monad"
where
  "as_user tptr f \<equiv> do
    tcb \<leftarrow> gets_the $ get_tcb tptr;
    uc \<leftarrow> return $ arch_tcb_context_get (tcb_arch tcb);
    (a, uc') \<leftarrow> select_f $ f uc;
    new_tcb \<leftarrow> return $ tcb \<lparr> tcb_arch := arch_tcb_context_set uc' (tcb_arch tcb)\<rparr>;
    set_object tptr (TCB new_tcb);
    return a
  od"

text {* Raise an exception if a property does not hold. *}
definition
throw_on_false :: "'e \<Rightarrow> (bool,'z::state_ext) s_monad \<Rightarrow> ('e + unit,'z::state_ext) s_monad" where
"throw_on_false ex f \<equiv> doE v \<leftarrow> liftE f; unlessE v $ throwError ex odE"

end
