(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invariants_AI
imports "./$L4V_ARCH/ArchInvariants_AI"
begin

context begin interpretation Arch .

requalify_types
  vs_chain
  vs_ref

requalify_consts
  not_kernel_window
  global_refs
  arch_obj_bits_type
  arch_cap_is_device
  is_nondevice_page_cap
  state_hyp_refs_of
  hyp_refs_of
  hyp_live

  wellformed_acap
  valid_arch_cap
  valid_arch_cap_ref
  acap_class
  valid_ipc_buffer_cap
  wellformed_vspace_obj
  arch_valid_obj
  valid_asid_map
  valid_vspace_obj
  valid_arch_tcb

  valid_arch_state
  valid_vspace_objs
  valid_arch_caps
  valid_global_objs
  valid_kernel_mappings
  equal_kernel_mappings
  valid_global_vspace_mappings
  pspace_in_kernel_window

  ASIDPoolObj

  vs_lookup1
  vs_lookup_trans
  vs_refs
  vs_lookup_pages1
  vs_lookup_pages_trans
  vs_refs_pages
  valid_vs_lookup
  user_mem
  device_mem
  device_region
  tcb_arch_ref

requalify_facts
  valid_arch_sizes
  aobj_bits_T
  valid_arch_cap_def2
  idle_global
  valid_ipc_buffer_cap_null
  valid_arch_cap_typ
  valid_vspace_obj_typ
  arch_kobj_size_bounded
  global_refs_lift
  valid_arch_state_lift
  aobj_at_default_arch_cap_valid
  aobj_ref_default
  acap_rights_update_id
  physical_arch_cap_has_ref
  wellformed_arch_default
  valid_vspace_obj_default'
  vs_lookup1_stateI2
  vs_lookup_pages1_stateI2
  typ_at_pg
  state_hyp_refs_of_elemD
  ko_at_state_hyp_refs_ofD
  hyp_sym_refs_obj_atD
  hyp_sym_refs_ko_atD
  state_hyp_refs_of_pspaceI
  state_hyp_refs_update
  hyp_refs_of_hyp_live
  hyp_refs_of_hyp_live_obj
  hyp_refs_of_simps
  tcb_arch_ref_simps
  hyp_live_tcb_simps
  hyp_live_tcb_def
  wellformed_arch_pspace
  wellformed_arch_typ
  valid_arch_tcb_pspaceI
  valid_arch_tcb_lift
  cte_level_bits_def
  arch_gen_obj_refs_inD
  obj_ref_not_arch_gen_ref
  arch_gen_ref_not_obj_ref
  same_aobject_same_arch_gen_refs
  valid_sc_size_less_word_bits

lemmas [simp] =
  tcb_bits_def
  endpoint_bits_def
  ntfn_bits_def

end

lemmas [intro!] =  idle_global acap_rights_update_id

lemmas [simp] =  acap_rights_update_id state_hyp_refs_update
                 tcb_arch_ref_simps hyp_live_tcb_simps hyp_refs_of_simps

(* Checking that vs_lookup notation is installed *)

term "vs_lookup :: 'z::state_ext state \<Rightarrow> vs_chain set"
term "(a \<rhd> b) :: ('z:: state_ext state) \<Rightarrow> bool"

-- ---------------------------------------------------------------------------
section "Invariant Definitions for Abstract Spec"

definition
  "is_ep ko \<equiv> case ko of Endpoint p \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_ntfn ko \<equiv> case ko of Notification p \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_tcb ko \<equiv> case ko of TCB t \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_cap_table bits ko \<equiv>
   case ko of CNode sz cs \<Rightarrow> bits = sz \<and> well_formed_cnode_n bits cs
            | _ \<Rightarrow> False"
definition
  "is_sc_obj n ko \<equiv> case ko of SchedContext sc n' \<Rightarrow> n = n' \<and> valid_sched_context_size n
                        | _ \<Rightarrow> False"
definition
  "is_reply ko \<equiv> case ko of Reply rply \<Rightarrow> True | _ \<Rightarrow> False"



abbreviation
  "ep_at \<equiv> obj_at is_ep"
abbreviation
  "ntfn_at \<equiv> obj_at is_ntfn"
abbreviation
  "tcb_at \<equiv> obj_at is_tcb"
abbreviation
  "cap_table_at bits \<equiv> obj_at (is_cap_table bits)"
abbreviation
  "real_cte_at cref \<equiv> cap_table_at (length (snd cref)) (fst cref)"
abbreviation
  "sc_at \<equiv> obj_at (\<lambda>ko. \<exists>n. is_sc_obj n ko)"
abbreviation
  "sc_obj_at n \<equiv> obj_at (is_sc_obj n)"
abbreviation
  "reply_at \<equiv> obj_at is_reply"


(*
 * sseefried: 'itcb' is projection of the "mostly preserved" fields of 'tcb'. Many functions
 * in the spec will leave these fields of a TCB unchanged. The 'crunch' tool is easily able
 * to ascertain this from the types of the fields.
 *
 * The 'itcb' record is closely associated with the 'pred_tcb_at' definition.
 * 'pred_tcb_at' is used to assert an arbitrary predicate over the fields in 'itcb' for a TCB
 * Before the introduction of this data structure 'st_tcb_at' was defined directly. It is
 * now an abbreviation of a partial application of the 'pred_tcb_at' function, specifically
 * a partial application to the projection function 'itcb_state'.
 *
 * The advantage of this approach is that we an assert 'pred_tcb_at proj P t' is preserved
 * across calls to many functions. We get "for free" that 'st_tcb_at P t' is also preserved.
 * In the future we may introduce other abbreviations that assert preservation over other
 * fields in the TCB record.
 *)
record itcb =
  itcb_state         :: thread_state
  itcb_ipc_buffer    :: vspace_ref
  itcb_fault         :: "fault option"
  itcb_bound_notification     :: "obj_ref option"
  itcb_sched_context :: "obj_ref option"
  itcb_yield_to :: "obj_ref option"
  itcb_mcpriority    :: priority


definition "tcb_to_itcb tcb \<equiv> \<lparr> itcb_state              = tcb_state tcb,
                                itcb_ipc_buffer         = tcb_ipc_buffer tcb,
                                itcb_fault              = tcb_fault tcb,
                                itcb_bound_notification = tcb_bound_notification tcb,
                                itcb_sched_context      = tcb_sched_context tcb,
                                itcb_yield_to           = tcb_yield_to tcb,
                                itcb_mcpriority         = tcb_mcpriority tcb\<rparr>"

(* sseefried: The simplification rules below are used to help produce
 * lemmas that talk about fields of the 'tcb' data structure rather than
 * the 'itcb' data structure when the lemma refers to a predicate of the
 * form 'pred_tcb_at proj P t'.
 *
 * e.g. You might have a lemma that has an assumption
 *   \<And>tcb. itcb_state (tcb_to_itcb (f tcb)) = itcb_state (tcb_to_itcb tcb)
 *
 * This simplifies to:
 *   \<And>tcb. tcb_state (f tcb) = tcb_state tcb
 *)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_state (tcb_to_itcb tcb) = tcb_state tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_ipc_buffer (tcb_to_itcb tcb) = tcb_ipc_buffer tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_fault (tcb_to_itcb tcb) = tcb_fault tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_bound_notification (tcb_to_itcb tcb) = tcb_bound_notification tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_sched_context (tcb_to_itcb tcb) = tcb_sched_context tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_yield_to (tcb_to_itcb tcb) = tcb_yield_to tcb"
  by (auto simp: tcb_to_itcb_def)

lemma [simp]: "itcb_mcpriority (tcb_to_itcb tcb) = tcb_mcpriority tcb"
 by (auto simp: tcb_to_itcb_def)

definition
  pred_tcb_at :: "(itcb \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "pred_tcb_at proj test \<equiv> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (proj (tcb_to_itcb tcb)))"

abbreviation "st_tcb_at \<equiv> pred_tcb_at itcb_state"
abbreviation "bound_tcb_at \<equiv> pred_tcb_at itcb_bound_notification"
abbreviation "bound_sc_tcb_at \<equiv> pred_tcb_at itcb_sched_context"
abbreviation "bound_yt_tcb_at \<equiv> pred_tcb_at itcb_yield_to"
abbreviation "mcpriority_tcb_at \<equiv> pred_tcb_at itcb_mcpriority"

(* sseefried: 'st_tcb_at_def' only exists to make existing proofs go through. Use 'pred_tcb_at_def' from now on. *)
lemma st_tcb_at_def: "st_tcb_at test \<equiv> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_state tcb))"
  by (simp add: pred_tcb_at_def)


text {* cte with property at *}


definition
  cte_wp_at :: "(cap \<Rightarrow> bool) \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "cte_wp_at P p s \<equiv> \<exists>cap. fst (get_cap p s) = {(cap,s)} \<and> P cap"

abbreviation
  cte_at :: "cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "cte_at \<equiv> cte_wp_at \<top>"


subsection "Valid caps and objects"

primrec
  untyped_range :: "cap \<Rightarrow> machine_word set"
where
  "untyped_range (cap.UntypedCap dev p n f)             = {p..p + (1 << n) - 1}"
| "untyped_range (cap.NullCap)                          = {}"
| "untyped_range (cap.EndpointCap r badge rights)       = {}"
| "untyped_range (cap.NotificationCap r badge rights)   = {}"
| "untyped_range (cap.CNodeCap r bits guard)            = {}"
| "untyped_range (cap.ThreadCap r)                      = {}"
| "untyped_range (cap.DomainCap)                        = {}"
| "untyped_range (cap.ReplyCap r)                       = {}"
| "untyped_range (cap.SchedContextCap r n)              = {}"
| "untyped_range (cap.SchedControlCap)                  = {}"
| "untyped_range (cap.IRQControlCap)                    = {}"
| "untyped_range (cap.IRQHandlerCap irq)                = {}"
| "untyped_range (cap.Zombie r b n)                     = {}"
| "untyped_range (cap.ArchObjectCap cap)                = {}"

primrec (nonexhaustive)
  usable_untyped_range :: "cap \<Rightarrow> machine_word set"
where
 "usable_untyped_range (UntypedCap _ p n f) =
  (if f < 2^n  then {p+of_nat f .. p + 2 ^ n - 1} else {})"

definition
  "obj_range p obj \<equiv> {p .. p + 2^obj_bits obj - 1}"

definition
  "pspace_no_overlap S \<equiv>
           \<lambda>s. \<forall>x ko. kheap s x = Some ko \<longrightarrow>
                {x .. x + (2 ^ obj_bits ko - 1)} \<inter> S = {}"

definition
  "valid_untyped c \<equiv> \<lambda>s.
  \<forall>p obj.
     kheap s p = Some obj \<longrightarrow>
     obj_range p obj \<inter> untyped_range c \<noteq> {} \<longrightarrow>
     ( obj_range p obj \<subseteq> untyped_range c \<and> usable_untyped_range c \<inter> obj_range p obj = {} )"

primrec
  cap_bits :: "cap \<Rightarrow> nat"
where
  "cap_bits NullCap = 0"
| "cap_bits (UntypedCap dev r b f) = b"
| "cap_bits (EndpointCap r b R) = obj_bits (Endpoint undefined)"
| "cap_bits (NotificationCap r b R) = obj_bits (Notification undefined)"
| "cap_bits (CNodeCap r b m) = cte_level_bits + b"
| "cap_bits (ThreadCap r) = obj_bits (TCB undefined)"
| "cap_bits (DomainCap) = 0"
| "cap_bits (ReplyCap r) = obj_bits (Reply undefined)"
| "cap_bits (Zombie r zs n) =
    (case zs of None \<Rightarrow> obj_bits (TCB undefined)
            | Some n \<Rightarrow> cte_level_bits + n)"
| "cap_bits (SchedContextCap r n) = n" (* RT: correct? *)
| "cap_bits (SchedControlCap) = 0"
| "cap_bits (IRQControlCap) = 0"
| "cap_bits (IRQHandlerCap irq) = 0"
| "cap_bits (ArchObjectCap x) = arch_obj_size x"

fun
  cap_is_device :: "cap \<Rightarrow> bool"
where
  "cap_is_device (cap.UntypedCap dev r b f) = dev"
| "cap_is_device (cap.ArchObjectCap x) = arch_cap_is_device x"
| "cap_is_device _ = False"

definition
  "cap_aligned c \<equiv>
   is_aligned (obj_ref_of c) (cap_bits c) \<and> cap_bits c < word_bits"


text {*
  Below, we define several predicates for capabilities on the abstract specification.
  Please note that we distinguish between well-formedness predicates,
  which merely refine the basic type and are independent of the kernel state,
  and the validity of the capability references,
  which necessarily depends on the current kernel state.

  Eventually, we will combine all predicates into @{text valid_cap}.
*}


definition
  wellformed_cap :: "cap \<Rightarrow> bool"
where
  "wellformed_cap c \<equiv>
  case c of
    UntypedCap dev p sz idx \<Rightarrow> untyped_min_bits \<le> sz
  | NotificationCap r badge rights \<Rightarrow> AllowGrant \<notin> rights
  | CNodeCap r bits guard \<Rightarrow> bits \<noteq> 0 \<and> length guard \<le> word_bits
  | IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ
  | Zombie r b n \<Rightarrow> (case b of None \<Rightarrow> n \<le> 5 (* RT? *)
                                          | Some b \<Rightarrow> n \<le> 2 ^ b \<and> b \<noteq> 0)
  | ArchObjectCap ac \<Rightarrow> wellformed_acap ac
  | SchedContextCap scp n \<Rightarrow> valid_sched_context_size n
  | _ \<Rightarrow> True"

definition
  valid_cap_ref :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cap_ref c s \<equiv> case c of
    NullCap \<Rightarrow> True
  | UntypedCap dev p b idx \<Rightarrow> valid_untyped c s \<and> idx \<le> 2^ b \<and> p \<noteq> 0
  | EndpointCap r badge rights \<Rightarrow> ep_at r s
  | NotificationCap r badge rights \<Rightarrow> ntfn_at r s
  | CNodeCap r bits guard \<Rightarrow> cap_table_at bits r s
  | ThreadCap r \<Rightarrow> tcb_at r s
  | DomainCap \<Rightarrow> True
  | ReplyCap r \<Rightarrow> reply_at r s
  | SchedContextCap r n \<Rightarrow> sc_obj_at n r s
  | SchedControlCap \<Rightarrow> True
  | IRQControlCap \<Rightarrow> True
  | IRQHandlerCap irq \<Rightarrow> True
  | Zombie r b n \<Rightarrow>
      (case b of None \<Rightarrow> tcb_at r s | Some b \<Rightarrow> cap_table_at b r s)
  | ArchObjectCap ac \<Rightarrow> valid_arch_cap_ref ac s"


definition
  valid_cap :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cap c s \<equiv> cap_aligned c \<and> (case c of
    NullCap \<Rightarrow> True
  | UntypedCap dev p b f \<Rightarrow> valid_untyped c s \<and> untyped_min_bits \<le> b \<and> f \<le> 2 ^ b \<and> p \<noteq> 0
  | EndpointCap r badge rights \<Rightarrow> ep_at r s
  | NotificationCap r badge rights \<Rightarrow>
         ntfn_at r s \<and> AllowGrant \<notin> rights
  | CNodeCap r bits guard \<Rightarrow>
         cap_table_at bits r s \<and> bits \<noteq> 0 \<and> length guard \<le> word_bits
  | ThreadCap r \<Rightarrow> tcb_at r s
  | DomainCap \<Rightarrow> True
  | ReplyCap r \<Rightarrow> reply_at r s
  | SchedContextCap r n \<Rightarrow> sc_obj_at n r s \<and> valid_sched_context_size n
  | SchedControlCap \<Rightarrow> True
  | IRQControlCap \<Rightarrow> True
  | IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ
  | Zombie r b n \<Rightarrow>
         (case b of None \<Rightarrow> tcb_at r s \<and> n \<le> 5 (* RT check *)
                  | Some b \<Rightarrow> cap_table_at b r s \<and> n \<le> 2 ^ b \<and> b \<noteq> 0)
  | ArchObjectCap ac \<Rightarrow> valid_arch_cap ac s)"


abbreviation
  valid_cap_syn :: "'z::state_ext state \<Rightarrow> cap \<Rightarrow> bool" ("_ \<turnstile> _" [60, 60] 61)
where
  "s \<turnstile> c \<equiv> valid_cap c s"

definition
  "valid_caps cs s \<equiv> \<forall>slot cap. cs slot = Some cap \<longrightarrow> valid_cap cap s"

primrec
  cap_class :: "cap \<Rightarrow> capclass"
where
  "cap_class (cap.NullCap)                          = NullClass"
| "cap_class (cap.UntypedCap dev p n f)             = PhysicalClass"
| "cap_class (cap.EndpointCap ref badge r)          = PhysicalClass"
| "cap_class (cap.NotificationCap ref badge r)      = PhysicalClass"
| "cap_class (cap.CNodeCap ref n bits)              = PhysicalClass"
| "cap_class (cap.ThreadCap ref)                    = PhysicalClass"
| "cap_class (cap.DomainCap)                        = DomainClass"
| "cap_class (cap.Zombie r b n)                     = PhysicalClass"
| "cap_class (cap.SchedContextCap r n)              = PhysicalClass"
| "cap_class (cap.SchedControlCap)                  = IRQClass" (* RT need a new one? *)
| "cap_class (cap.IRQControlCap)                    = IRQClass"
| "cap_class (cap.IRQHandlerCap irq)                = IRQClass"
| "cap_class (cap.ReplyCap tcb)                     = PhysicalClass"
| "cap_class (cap.ArchObjectCap cap)                = acap_class cap"


definition
  valid_cs_size :: "nat \<Rightarrow> cnode_contents \<Rightarrow> bool" where
  "valid_cs_size sz cs \<equiv>
  sz < word_bits - cte_level_bits \<and> well_formed_cnode_n sz cs"

definition
  valid_cs :: "nat \<Rightarrow> cnode_contents \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_cs sz cs s \<equiv> (\<forall>cap \<in> ran cs. s \<turnstile> cap) \<and> valid_cs_size sz cs"

definition
  valid_tcb_state :: "thread_state \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_tcb_state ts s \<equiv> case ts of
    BlockedOnReceive ref r \<Rightarrow> ep_at ref s \<and> (case r of Some r' \<Rightarrow> reply_at r' s | _ \<Rightarrow> True)
  | BlockedOnSend ref sp \<Rightarrow> ep_at ref s
  | BlockedOnNotification ref \<Rightarrow> ntfn_at ref s
  | BlockedOnReply r \<Rightarrow> (case r of Some r' \<Rightarrow> reply_at r' s | _ \<Rightarrow> True)
  | _ \<Rightarrow> True"

abbreviation
  "inactive st \<equiv> st = Inactive"

abbreviation
  "halted st \<equiv> case st of
                     Inactive \<Rightarrow> True
                   | IdleThreadState \<Rightarrow> True
                   | _ \<Rightarrow> False"

definition
  tcb_cap_cases ::
  "cap_ref \<rightharpoonup> ((tcb \<Rightarrow> cap) \<times>
               ((cap \<Rightarrow> cap) \<Rightarrow> tcb \<Rightarrow> tcb) \<times>
               (obj_ref \<Rightarrow> thread_state \<Rightarrow> cap \<Rightarrow> bool))"
where
  "tcb_cap_cases \<equiv>
   [tcb_cnode_index 0 \<mapsto> (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>)),
    tcb_cnode_index 1 \<mapsto> (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>)),
    tcb_cnode_index 2 \<mapsto> (tcb_ipcframe, tcb_ipcframe_update,
                          (\<lambda>_ _. is_nondevice_page_cap or (op = NullCap))),
    tcb_cnode_index 3 \<mapsto> (tcb_fault_handler, tcb_fault_handler_update, (\<lambda>_ _. \<top>)),
    tcb_cnode_index 4 \<mapsto> (tcb_timeout_handler, tcb_timeout_handler_update, (\<lambda>_ _. \<top>))]"
                                  (* RT: check the handler cases *)

definition
  valid_fault :: "ExceptionTypes_A.fault \<Rightarrow> bool"
where
  "valid_fault f \<equiv>
   \<forall>mw b n g. f = (ExceptionTypes_A.CapFault mw b
                     (ExceptionTypes_A.GuardMismatch n g)) \<longrightarrow> length g\<le>word_bits"

definition
  valid_bound_obj :: "(machine_word \<Rightarrow> 'z state \<Rightarrow> bool) \<Rightarrow> machine_word option \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_bound_obj f p_opt s \<equiv> case p_opt of
                                 None \<Rightarrow> True
                               | Some p \<Rightarrow> f p s"

abbreviation
  "valid_bound_ntfn \<equiv> valid_bound_obj ntfn_at"

abbreviation
  "valid_bound_tcb \<equiv> valid_bound_obj tcb_at"

abbreviation
  "valid_bound_sc \<equiv> valid_bound_obj sc_at"

abbreviation
  "valid_bound_reply \<equiv> valid_bound_obj reply_at"

definition
  valid_ntfn :: "notification \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ntfn ntfn s \<equiv> (case ntfn_obj ntfn of
    IdleNtfn \<Rightarrow>  True
  | WaitingNtfn ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s)
       \<and> distinct ts
       \<and> (case ntfn_bound_tcb ntfn of Some tcb \<Rightarrow> ts = [tcb] | _ \<Rightarrow> True))
  | ActiveNtfn b \<Rightarrow> True)
 \<and> valid_bound_tcb (ntfn_bound_tcb ntfn) s
 \<and> valid_bound_sc (ntfn_sc ntfn) s"

definition
  valid_tcb :: "obj_ref \<Rightarrow> tcb \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_tcb p t s \<equiv>
     (\<forall>(getF, setF, restr) \<in> ran tcb_cap_cases.
       s \<turnstile> getF t \<and> restr p (tcb_state t) (getF t))
     \<and> valid_ipc_buffer_cap (tcb_ipcframe t) (tcb_ipc_buffer t)
     \<and> valid_tcb_state (tcb_state t) s
     \<and> (case tcb_fault t of Some f \<Rightarrow> valid_fault f | _ \<Rightarrow> True)
     \<and> valid_bound_ntfn (tcb_bound_notification t) s
     \<and> valid_bound_sc (tcb_sched_context t) s
     \<and> valid_bound_sc (tcb_yield_to t) s
     \<and> valid_arch_tcb (tcb_arch t) s"

definition
  tcb_cap_valid :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_cap_valid cap ptr s \<equiv> tcb_at (fst ptr) s \<longrightarrow>
     st_tcb_at (\<lambda>st. case tcb_cap_cases (snd ptr) of
                          Some (getF, setF, restr) \<Rightarrow> restr (fst ptr) st cap
                        | None \<Rightarrow> True)
               (fst ptr) s
      \<and> (snd ptr = tcb_cnode_index 2 \<longrightarrow>
           (\<forall>tcb. ko_at (TCB tcb) (fst ptr) s
                   \<longrightarrow> valid_ipc_buffer_cap cap (tcb_ipc_buffer tcb)))"

definition
  valid_ep :: "endpoint \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ep ep s \<equiv> case ep of
    IdleEP \<Rightarrow> True
  | SendEP ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s) \<and> distinct ts)
  | RecvEP ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s) \<and> distinct ts)"

definition
  valid_sched_context :: "sched_context \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_sched_context sc s \<equiv> (* RT FIXME: any conditions for period consumed refills refill_max? *)
     valid_bound_ntfn (sc_ntfn sc) s
     \<and> valid_bound_tcb (sc_tcb sc) s
     \<and> valid_bound_tcb (sc_yield_from sc) s
     \<and> list_all (\<lambda>r. reply_at r s) (sc_replies sc)
     \<and> length (sc_refills sc) \<ge> 1
     (* \<and> length (sc_replies sc) \<le> sc_refill_max sc *)"

definition
  valid_reply :: "reply \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_reply reply s \<equiv>
     valid_bound_tcb (reply_tcb reply) s
     \<and> valid_bound_sc (reply_sc reply) s"


definition
  valid_obj :: "obj_ref \<Rightarrow> kernel_object \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_obj ptr ko s \<equiv> case ko of
    Endpoint p \<Rightarrow> valid_ep p s
  | Notification p \<Rightarrow> valid_ntfn p s
  | TCB t \<Rightarrow> valid_tcb ptr t s
  | CNode sz cs \<Rightarrow> valid_cs sz cs s
  | SchedContext sc n \<Rightarrow> valid_sched_context sc s \<and> valid_sched_context_size n
  | Reply reply \<Rightarrow> valid_reply reply s
  | ArchObj ao \<Rightarrow> arch_valid_obj ao s"

definition
  valid_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_objs s \<equiv> \<forall>ptr \<in> dom $ kheap s. \<exists>obj. kheap s ptr = Some obj \<and> valid_obj ptr obj s"

text {* simple kernel objects *}

lemma obj_at_eq_helper:
  "\<lbrakk> \<And>obj. P obj = P' obj \<rbrakk> \<Longrightarrow> obj_at P = obj_at P'"
  apply (rule ext)+
  apply (simp add: obj_at_def)
  done

lemma is_ep_def2: "(is_ep ko) = bound (partial_inv Endpoint ko)"
  by (auto simp: is_ep_def split: kernel_object.splits)

lemma ep_at_def2: "ep_at = (obj_at (\<lambda>ko. bound (partial_inv Endpoint ko)))"
  by (rule obj_at_eq_helper, simp add: is_ep_def2)

lemma is_ntfn_def2: "(is_ntfn ko) = bound (partial_inv Notification ko)"
  by (auto simp: is_ntfn_def split: kernel_object.splits)

lemma ntfn_at_def2: "ntfn_at = (obj_at (\<lambda>ko. bound (partial_inv Notification ko)))"
  by (rule obj_at_eq_helper, simp add: is_ntfn_def2)

lemma is_reply_def2: "(is_reply ko) = bound (partial_inv Reply ko)"
  by (auto simp: is_reply_def split: kernel_object.splits)

lemma reply_at_def2: "reply_at = (obj_at (\<lambda>ko. bound (partial_inv Reply ko)))"
  by (rule obj_at_eq_helper, simp add: is_reply_def2)

definition
  valid_simple_obj :: "kernel_object \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_simple_obj ko s \<equiv> case ko of
    Endpoint p \<Rightarrow> valid_ep p s
  | Notification p \<Rightarrow> valid_ntfn p s
  | TCB t \<Rightarrow> True
  | CNode sz cs \<Rightarrow> True
  | SchedContext sc n \<Rightarrow> True
  | Reply reply \<Rightarrow> valid_reply reply s
  | ArchObj ao \<Rightarrow> arch_valid_obj ao s"

definition
  valid_simple_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_simple_objs s \<equiv> \<forall>ptr \<in> dom $ kheap s. \<exists>obj. kheap s ptr = Some obj \<and> valid_simple_obj obj s"

lemma valid_obj_imp_valid_simple: "valid_obj p ko s \<Longrightarrow> valid_simple_obj ko s"
  by (clarsimp simp: valid_obj_def valid_simple_obj_def split: kernel_object.splits)

lemma valid_objs_imp_valid_simple_objs: "valid_objs s \<Longrightarrow> valid_simple_objs s"
  by (fastforce simp: valid_obj_imp_valid_simple valid_objs_def valid_simple_objs_def
                split: kernel_object.splits)

declare valid_simple_obj_def[simp]

lemma valid_ep_def2: "valid_ep = (\<lambda>x s. valid_simple_obj (Endpoint x) s)"
  by simp

lemma valid_ntfn_def2: "valid_ntfn = (\<lambda>x s. valid_simple_obj (Notification x) s)"
  by simp

lemma valid_reply_def2: "valid_reply = (\<lambda>x s. valid_simple_obj (Reply x) s)"
  by simp

lemma valid_simple_kheap:"\<lbrakk>kheap s p = Some v ;
                 a_type v \<in> {AEndpoint, ANTFN, AReply} \<rbrakk>\<Longrightarrow> valid_obj p v s = valid_simple_obj v s"
  by (auto simp: valid_obj_imp_valid_simple valid_obj_def a_type_def
           split: kernel_object.splits if_splits)

abbreviation
  "simple_typ_at \<equiv> obj_at (\<lambda>ob. a_type ob \<in> {AEndpoint, ANTFN, AReply})"

lemmas is_simple_ko_defs = is_ep_def is_ntfn_def is_reply_def

text {* symref related definitions *}

definition
  tcb_st_refs_of :: "thread_state  \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_st_refs_of z \<equiv> case z of (Running)               => {}
  | (Inactive)              => {}
  | (Restart)               => {}
  | (BlockedOnReply r)        => if bound r then {(the r, TCBReply)} else {}
  | (IdleThreadState)       => {}
  | (BlockedOnReceive x r)  => if bound r then {(x, TCBBlockedRecv), (the r, TCBReply)}
                               else {(x, TCBBlockedRecv)}
  | (BlockedOnSend x payl)  => {(x, TCBBlockedSend)}
  | (BlockedOnNotification x) => {(x, TCBSignal)}"

definition
  ep_q_refs_of   :: "endpoint      \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "ep_q_refs_of x \<equiv> case x of
    IdleEP    => {}
  | (RecvEP q) => set q \<times> {EPRecv}
  | (SendEP q) => set q \<times> {EPSend}"

definition
  ntfn_q_refs_of  :: "ntfn                   \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "ntfn_q_refs_of x \<equiv> case x of
     IdleNtfn         => {}
  | (WaitingNtfn q)   => set q \<times> {NTFNSignal}
  | (ActiveNtfn b)  => {}"

(* FIXME-NTFN: two new functions: ntfn_bound_refs and tcb_bound_refs, include below by union *)

definition
  get_refs :: "reftype \<Rightarrow> obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "get_refs ref ptr_opt \<equiv> case ptr_opt of
     Some ptr \<Rightarrow> {(ptr, ref)}
   | None \<Rightarrow> {}"

definition
  refs_of_tcb :: "tcb \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_tcb tcb \<equiv> tcb_st_refs_of (tcb_state tcb)
                          \<union> get_refs TCBBound (tcb_bound_notification tcb)
                          \<union> get_refs TCBSchedContext (tcb_sched_context tcb)
                          \<union> get_refs TCBYieldTo (tcb_yield_to tcb)"

definition
  refs_of_ntfn :: "notification \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_ntfn ntfn \<equiv> ntfn_q_refs_of (ntfn_obj ntfn)
                          \<union> get_refs NTFNBound (ntfn_bound_tcb ntfn)
                          \<union> get_refs NTFNSchedContext (ntfn_sc ntfn)"

definition
  refs_of_sc :: "sched_context \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_sc sc \<equiv> get_refs SCNtfn (sc_ntfn sc)
                          \<union> get_refs SCTcb (sc_tcb sc)
                          \<union> get_refs SCYieldFrom (sc_yield_from sc)
                          \<union> set (map (\<lambda>r. (r, SCReply)) (sc_replies sc))"

definition
  refs_of_reply :: "reply \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of_reply r \<equiv> get_refs ReplySchedContext (reply_sc r)
                          \<union> get_refs ReplyTCB (reply_tcb r)"

lemmas refs_of_defs[simp] = refs_of_tcb_def refs_of_ntfn_def refs_of_sc_def refs_of_reply_def

definition
  refs_of :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of x \<equiv> case x of
     CNode sz fun      => {}
   | TCB tcb           => refs_of_tcb tcb
   | Endpoint ep       => ep_q_refs_of ep
   | Notification ntfn => refs_of_ntfn ntfn
   | SchedContext sc n \<Rightarrow> refs_of_sc sc
   | Reply r           \<Rightarrow> refs_of_reply r
   | ArchObj ao        => {}"

definition
  state_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
 "state_refs_of s \<equiv> \<lambda>x. case (kheap s x) of Some ko \<Rightarrow> refs_of ko | None \<Rightarrow> {}"

definition all_refs_of :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set"
where "all_refs_of x \<equiv> refs_of x \<union> hyp_refs_of x"

definition
  state_all_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
 "state_all_refs_of s \<equiv> \<lambda>x. case (kheap s x) of Some ko \<Rightarrow> refs_of ko | None \<Rightarrow> {}"

text "objects live in device_region or non_device_region"

definition
  pspace_respects_device_region:: "'z::state_ext state \<Rightarrow> bool"
where
 "pspace_respects_device_region \<equiv> \<lambda>s. (dom (user_mem s)) \<subseteq> - (device_region s)
 \<and> (dom (device_mem s)) \<subseteq> (device_region s)"

definition live_sc :: "sched_context \<Rightarrow> bool"
where
  "live_sc sc \<equiv> (bound (sc_tcb sc) \<or> bound (sc_yield_from sc) \<or> bound (sc_ntfn sc)
                                \<or> (sc_replies sc \<noteq> []))"

definition live_ntfn :: "notification \<Rightarrow> bool"
where
  "live_ntfn ntfn \<equiv> (bound (ntfn_bound_tcb ntfn) \<or> bound (ntfn_sc ntfn)
                                \<or> (\<exists>ts. ntfn_obj ntfn = WaitingNtfn ts))"

primrec
  live0 :: "kernel_object \<Rightarrow> bool"
where
  "live0 (CNode sz fun)      = False"
| "live0 (TCB tcb)           = (bound (tcb_bound_notification tcb) \<or> bound (tcb_sched_context tcb)
                                \<or> bound (tcb_yield_to tcb)
                                \<or> tcb_state tcb \<noteq> Inactive \<and> tcb_state tcb \<noteq> IdleThreadState)"
| "live0 (Endpoint ep)       = (ep \<noteq> IdleEP)"
| "live0 (SchedContext sc n) = live_sc sc"
| "live0 (Reply reply)       = (bound (reply_tcb reply) \<or> bound (reply_sc reply))"
| "live0 (Notification ntfn) = live_ntfn ntfn"
| "live0 (ArchObj ao)        = False"

definition live :: "kernel_object \<Rightarrow> bool"
where
 "live ko \<equiv> case ko of
     CNode sz fun      => False
   | TCB tcb           => live0 ko \<or> hyp_live ko
   | Endpoint ep       => live0 ko
   | Notification ntfn => live0 ko
   | SchedContext sc n => live0 ko
   | Reply reply       => live0 ko
   | ArchObj ao        => hyp_live ko"

lemma a_type_arch_live:
  "a_type ko = AArch tp \<Longrightarrow> \<not> live0 ko"
  by (simp add: a_type_def
         split: Structures_A.kernel_object.split_asm if_splits)

fun
  zobj_refs :: "cap \<Rightarrow> obj_ref set"
where
  "zobj_refs (Zombie r b n) = {}"
| "zobj_refs x                  = obj_refs x"

definition
  ex_nonz_cap_to :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "ex_nonz_cap_to ref \<equiv> (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>c. ref \<in> zobj_refs c) cref s)"

text {* All live objects have caps. The contrapositive
        of this is significant in establishing invariants
        over retype. The exception are objects that are
        not in the scope of any untyped capability, as
        these can never be retyped. *}
definition
  if_live_then_nonz_cap :: "'z::state_ext state \<Rightarrow> bool"
where
 "if_live_then_nonz_cap s \<equiv>
    \<forall>ptr. obj_at live ptr s \<longrightarrow> ex_nonz_cap_to ptr s"

primrec
  cte_refs :: "cap \<Rightarrow> (irq \<Rightarrow> obj_ref) \<Rightarrow> cslot_ptr set"
where
  "cte_refs (UntypedCap dev p n fr) f                = {}"
| "cte_refs (NullCap) f                          = {}"
| "cte_refs (EndpointCap r badge rights) f       = {}"
| "cte_refs (NotificationCap r badge rights) f  = {}"
| "cte_refs (CNodeCap r bits guard) f            =
     {r} \<times> {xs. length xs = bits}"
| "cte_refs (ThreadCap r) f                      =
     {r} \<times> (dom tcb_cap_cases)"
| "cte_refs (DomainCap) f                        = {}"
| "cte_refs (Zombie r b n) f                     =
     {r} \<times> {xs. length xs = (zombie_cte_bits b) \<and>
                unat (of_bl xs :: machine_word) < n}"
| "cte_refs (SchedContextCap r n) f                    = {}"
| "cte_refs (SchedControlCap) f                    = {}"
| "cte_refs (IRQControlCap) f                    = {}"
| "cte_refs (IRQHandlerCap irq) f                = {(f irq, [])}"
| "cte_refs (ReplyCap r) f              = {}"
| "cte_refs (ArchObjectCap cap) f                = {}"

definition
  ex_cte_cap_wp_to :: "(cap \<Rightarrow> bool) \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "ex_cte_cap_wp_to P ptr \<equiv> \<lambda>s. \<exists>cref.
        cte_wp_at (\<lambda>c. P c \<and> ptr \<in> cte_refs c (interrupt_irq_node s)) cref s"

abbreviation
 "ex_cte_cap_to \<equiv> ex_cte_cap_wp_to \<top>"

(* All non-Null caps live either in capability tables to which there
   are appropriate existing capabilities. *)

definition
  appropriate_cte_cap :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "appropriate_cte_cap cap cte_cap \<equiv>
  case cap of
    NullCap \<Rightarrow> True
  | NotificationCap _ _ _ \<Rightarrow> True
  | _ \<Rightarrow> cap_irqs cte_cap = {}"

definition
  if_unsafe_then_cap :: "'z::state_ext state \<Rightarrow> bool"
where
 "if_unsafe_then_cap s \<equiv> \<forall>cref cap. caps_of_state s cref = Some cap
                         \<longrightarrow> cap \<noteq> NullCap
                        \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) cref s"

text {* All zombies are final. *}
definition
  zombies_final :: "'z::state_ext state \<Rightarrow> bool"
where
 "zombies_final \<equiv>
  \<lambda>s. \<forall>p. cte_wp_at is_zombie p s \<longrightarrow> cte_wp_at (\<lambda>cap. is_final_cap' cap s) p s"

definition
  valid_pspace :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_pspace \<equiv> valid_objs and pspace_aligned and
                  pspace_distinct and if_live_then_nonz_cap
                  and zombies_final
                  and (\<lambda>s. sym_refs (state_refs_of s))
                  and (\<lambda>s. sym_refs (state_hyp_refs_of s))"

definition
  null_filter :: "('a \<Rightarrow> cap option) \<Rightarrow> ('a \<Rightarrow> cap option)"
where
  "null_filter f \<equiv> (\<lambda>x. if f x = Some NullCap then None else f x)"

definition
  untyped_mdb :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "untyped_mdb m cs \<equiv>
  \<forall>ptr ptr' cap cap'.
      cs ptr = Some cap \<longrightarrow> is_untyped_cap cap \<longrightarrow>
      cs ptr' = Some cap' \<longrightarrow> obj_refs cap' \<inter> untyped_range cap \<noteq> {} \<longrightarrow>
      ptr' \<in> descendants_of ptr m"

text "inclusion properties on untyped caps"
definition
  untyped_inc :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
  "untyped_inc m cs \<equiv>
  \<forall>p p' c c'.
     cs p = Some c \<longrightarrow> is_untyped_cap c \<longrightarrow>
     cs p' = Some c' \<longrightarrow> is_untyped_cap c' \<longrightarrow>
     (untyped_range c \<subseteq> untyped_range c' \<or>
      untyped_range c' \<subseteq> untyped_range c \<or>
      untyped_range c \<inter> untyped_range c' = {}) \<and>
     (untyped_range c \<subset> untyped_range c' \<longrightarrow> (p \<in> descendants_of p' m \<and> untyped_range c \<inter> usable_untyped_range c' = {})) \<and>
     (untyped_range c' \<subset> untyped_range c \<longrightarrow> (p' \<in> descendants_of p m \<and> untyped_range c' \<inter> usable_untyped_range c = {})) \<and>
     (untyped_range c = untyped_range c' \<longrightarrow>
       (p' \<in> descendants_of p m \<and> usable_untyped_range c = {} \<or> p \<in> descendants_of p' m \<and> usable_untyped_range c' = {} \<or> p = p'))"

definition
  "cap_range c \<equiv> untyped_range c \<union> obj_refs c"

definition
  descendants_inc :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
  "descendants_inc m cs \<equiv>
  \<forall>p p'. p \<in> descendants_of p' m \<longrightarrow> (cap_class (the (cs p)) = cap_class (the (cs p')) \<and> cap_range (the (cs p)) \<subseteq> cap_range (the (cs p')))"

abbreviation
  "awaiting_reply ts \<equiv> (case ts of BlockedOnReply _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "valid_ioc s \<equiv>
   \<forall>p. is_original_cap s p \<longrightarrow> cte_wp_at (\<lambda>x. x \<noteq> NullCap)  p s"

definition
  "has_reply_cap t s \<equiv> \<exists>p. cte_wp_at (op = (ReplyCap t)) p s"

definition
  "mdb_cte_at ct_at m \<equiv> \<forall>p c. m c = Some p \<longrightarrow> ct_at p \<and> ct_at c"

definition
  "no_mloop m \<equiv> \<forall>p. \<not> m \<Turnstile> p \<rightarrow> p"

definition
  "ut_revocable r cs \<equiv> \<forall>p cap. cs p = Some cap \<longrightarrow> is_untyped_cap cap \<longrightarrow> r p"

definition
  "irq_revocable r cs \<equiv> \<forall>p. cs p = Some IRQControlCap \<longrightarrow> r p"

definition
  "valid_mdb \<equiv> \<lambda>s. mdb_cte_at (swp (cte_wp_at (op \<noteq> NullCap)) s) (cdt s) \<and>
                   untyped_mdb (cdt s) (caps_of_state s) \<and> descendants_inc (cdt s) (caps_of_state s) \<and>
                   no_mloop (cdt s) \<and> untyped_inc (cdt s) (caps_of_state s) \<and>
                   ut_revocable (is_original_cap s) (caps_of_state s) \<and>
                   irq_revocable (is_original_cap s) (caps_of_state s)"

abbreviation
  "idle_tcb_at \<equiv> pred_tcb_at (\<lambda>t. (itcb_state t, itcb_bound_notification t,
                                    itcb_sched_context t, itcb_yield_to t))"

definition
  "valid_idle \<equiv> \<lambda>s. idle_tcb_at (\<lambda>(st, ntfn, sc, yt).
       (idle st) \<and> (ntfn  = None) \<and> (sc = Some idle_sc_ptr) \<and> (yt = None)) (idle_thread s) s
         \<and> idle_thread s = idle_thread_ptr"

definition
  "only_idle \<equiv> \<lambda>s. \<forall>t. st_tcb_at idle t s \<longrightarrow> t = idle_thread s"

definition
  valid_refs :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refs R \<equiv> \<lambda>s. \<forall>cref. \<not>cte_wp_at (\<lambda>c. R \<inter> cap_range c \<noteq> {}) cref s"

text "caps point at objects in the kernel window"
definition
  cap_refs_in_kernel_window :: "'z::state_ext state \<Rightarrow> bool"
where
 "cap_refs_in_kernel_window \<equiv> \<lambda>s. valid_refs (not_kernel_window s) s"


definition
  valid_global_refs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_refs \<equiv> \<lambda>s. valid_refs (global_refs s) s"

definition
  valid_irq_node :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_irq_node \<equiv> \<lambda>s. inj (interrupt_irq_node s)
      \<and> (\<forall>irq. cap_table_at 0 (interrupt_irq_node s irq) s)"

definition
  irq_issued :: "irq \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "irq_issued irq \<equiv> \<lambda>s. interrupt_states s irq = irq_state.IRQSignal"

definition
  valid_irq_handlers :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_irq_handlers \<equiv> \<lambda>s. \<forall>cap \<in> ran (caps_of_state s). \<forall>irq \<in> cap_irqs cap. irq_issued irq s"

definition valid_irq_masks :: "(irq \<Rightarrow> irq_state) \<Rightarrow> (irq \<Rightarrow> bool) \<Rightarrow> bool" where
  "valid_irq_masks table masked \<equiv> \<forall>irq. table irq = IRQInactive \<longrightarrow> masked irq"

definition valid_irq_states :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_irq_states \<equiv> \<lambda>s.
    valid_irq_masks (interrupt_states s) (irq_masks (machine_state s))"

definition "cap_range_respects_device_region c s \<equiv>
  if (cap_is_device c) then cap_range c \<subseteq> device_region s
  else cap_range c \<subseteq> - device_region s"

definition
  cap_refs_respects_device_region :: "'z::state_ext state \<Rightarrow> bool"
where
 "cap_refs_respects_device_region \<equiv> \<lambda>s. \<forall>cref.
   \<not> cte_wp_at (\<lambda>c. \<not> cap_range_respects_device_region  c s) cref s"

definition
  "valid_machine_state \<equiv>
   \<lambda>s. \<forall>p. in_user_frame p (s::'z::state_ext state) \<or> underlying_memory (machine_state s) p = 0"

definition
  valid_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_state \<equiv> valid_pspace
                  and valid_mdb
                  and valid_ioc
                  and valid_idle
                  and only_idle
                  and if_unsafe_then_cap
                  and valid_global_refs
                  and valid_arch_state
                  and valid_irq_node
                  and valid_irq_handlers
                  and valid_irq_states
                  and valid_machine_state
                  and valid_vspace_objs
                  and valid_arch_caps
                  and valid_global_objs
                  and valid_kernel_mappings
                  and equal_kernel_mappings
                  and valid_asid_map
                  and valid_global_vspace_mappings
                  and pspace_in_kernel_window
                  and cap_refs_in_kernel_window
                  and pspace_respects_device_region
                  and cap_refs_respects_device_region"

definition
 "ct_in_state test \<equiv> \<lambda>s. st_tcb_at test (cur_thread s) s"

definition
  "cur_tcb s \<equiv> tcb_at (cur_thread s) s"

definition
  invs :: "'z::state_ext state \<Rightarrow> bool" where
  "invs \<equiv> valid_state and cur_tcb"


subsection "Derived concepts"

definition
  untyped_children_in_mdb :: "'z::state_ext state \<Rightarrow> bool"
where
 "untyped_children_in_mdb s \<equiv>
    \<forall>ptr ptr' cap. (cte_wp_at (op = cap) ptr s \<and> is_untyped_cap cap
                     \<and> cte_wp_at (\<lambda>cap'. obj_refs cap' \<inter> untyped_range cap \<noteq> {}) ptr' s)
                     \<longrightarrow> ptr' \<in> descendants_of ptr (cdt s)"

definition
  "caps_contained s \<equiv> \<forall>c p c' p'.
  cte_wp_at (op = c) p s \<longrightarrow>
  cte_wp_at (op = c') p' s \<longrightarrow>
  obj_ref_of c' \<in> untyped_range c \<longrightarrow>
  (is_cnode_cap c' \<or> is_thread_cap c') \<longrightarrow>
  obj_ref_of c' + obj_size c' - 1 \<in> untyped_range c"

definition
  "obj_bits_type T \<equiv> case T of
    ACapTable n \<Rightarrow> cte_level_bits + n
  | AGarbage n \<Rightarrow> n
  | ATCB \<Rightarrow> obj_bits (TCB undefined)
  | AEndpoint \<Rightarrow> obj_bits (Endpoint undefined)
  | ANTFN \<Rightarrow> obj_bits (Notification undefined)
  | ASchedContext n \<Rightarrow> n
  | AReply \<Rightarrow> obj_bits (Reply undefined)
  | AArch T' \<Rightarrow> arch_obj_bits_type T'"

definition
  "typ_range p T \<equiv> {p .. p + 2^obj_bits_type T - 1}"

abbreviation (* RT: should YieldTo be added here? *)
  "active st \<equiv> st = Running \<or> st = Restart"

abbreviation (* RT: should YieldTo be added here? probably no *)
  "simple st \<equiv> st = Inactive \<or>
                 st = Running \<or>
                 st = Restart \<or> (* (\<exists>t. st = YieldTo t) \<or>*)
                 idle st \<or> awaiting_reply st"
abbreviation
  "ct_active \<equiv> ct_in_state active"

abbreviation
  "ct_running  \<equiv> ct_in_state  (\<lambda>st. st = Running)"

abbreviation
  "ct_idle \<equiv> ct_in_state idle"

abbreviation(input)
 "all_invs_but_sym_refs
    \<equiv> valid_objs and pspace_aligned and pspace_distinct and valid_ioc
       and if_live_then_nonz_cap and zombies_final
       and valid_mdb and valid_idle and only_idle and if_unsafe_then_cap
       and valid_global_refs
       and valid_arch_state and valid_machine_state and valid_irq_states
       and valid_irq_node and valid_irq_handlers and valid_vspace_objs
       and valid_arch_caps and valid_global_objs and valid_kernel_mappings
       and equal_kernel_mappings and valid_asid_map
       and valid_global_vspace_mappings
       and pspace_in_kernel_window and cap_refs_in_kernel_window
       and pspace_respects_device_region and cap_refs_respects_device_region
       and cur_tcb"


-- ---------------------------------------------------------------------------
section "Lemmas"

lemma valid_bound_obj_None[simp]:
  "valid_bound_obj f None = \<top>"
  by (auto simp: valid_bound_obj_def)

lemma valid_bound_obj_Some[simp]:
  "valid_bound_obj f (Some x) = f x"
  by (auto simp: valid_bound_obj_def)

lemmas wellformed_cap_simps = wellformed_cap_def[split_simps cap.split]

lemmas valid_cap_ref_simps =
  valid_cap_ref_def[split_simps cap.split]

lemmas valid_cap_simps = valid_cap_def[split_simps cap.split]

lemma is_ep:
  "is_ep ko = (\<exists>ep. ko = Endpoint ep)"
  unfolding is_ep_def by (cases ko) auto

lemma is_ntfn:
  "is_ntfn ko = (\<exists>ep. ko = Notification ep)"
  unfolding is_ntfn_def by (cases ko) auto

lemma is_tcb:
  "is_tcb ko = (\<exists>tcb. ko = TCB tcb)"
  unfolding is_tcb_def by (cases ko) auto

lemma is_reply:
  "is_reply ko = (\<exists>reply. ko = Reply reply)"
  unfolding is_reply_def by (cases ko) auto

lemma is_cap_table:
  "is_cap_table bits ko =
  (\<exists>cs. ko = CNode bits cs \<and> well_formed_cnode_n bits cs)"
  unfolding is_cap_table_def by (cases ko) auto

lemmas is_obj_defs = is_ep is_ntfn is_tcb is_reply is_cap_table is_sc_obj_def

-- "sanity check"
lemma obj_at_get_object:
  "obj_at P ref s \<Longrightarrow> fst (get_object ref s) \<noteq> {}"
  by (auto simp: obj_at_def get_object_def gets_def get_def
                 return_def assert_def bind_def)

lemma ko_at_tcb_at:
  "ko_at (TCB t) p s \<Longrightarrow> tcb_at p s"
  by (simp add: obj_at_def is_tcb)

lemma tcb_at_def:
  "tcb_at t s = (\<exists>tcb. get_tcb t s = Some tcb)"
  by (simp add: obj_at_def get_tcb_def is_tcb_def
           split: option.splits kernel_object.splits)

lemma pred_tcb_def2:
  "pred_tcb_at proj test addr s = (\<exists>tcb. (get_tcb addr s) = Some tcb \<and> test (proj (tcb_to_itcb tcb)))"
  by (simp add: obj_at_def pred_tcb_at_def get_tcb_def
            split: option.splits kernel_object.splits)

(* sseefried: 'st_tcb_def2' only exists to make existing proofs go through. Can use 'pred_tcb_at_def2' instead *)
lemmas st_tcb_def2 = pred_tcb_def2[where proj=itcb_state,simplified]

lemma tcb_at_typ:
  "tcb_at = typ_at ATCB"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_tcb_def a_type_def
            split: kernel_object.splits)
  done

lemma ntfn_at_typ:
  "ntfn_at = typ_at ANTFN"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_ntfn_def a_type_def
            split: kernel_object.splits)
  done

lemma ep_at_typ:
  "ep_at = typ_at AEndpoint"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_ep_def a_type_def
            split: kernel_object.splits)
  done

lemma sc_obj_at_typ:
  "sc_obj_at n = typ_at (ASchedContext n)"
  apply (rule obj_at_eq_helper)
  apply (auto simp add: is_sc_obj_def a_type_def
            split: kernel_object.splits)
  done

lemma sc_at_typ:
 "sc_at = (\<lambda>p s. \<exists>n. typ_at (ASchedContext n) p s)"
  apply (rule ext)+
  apply (auto simp add: obj_at_def is_sc_obj_def)
   apply (rule_tac x=n in exI, case_tac ko; clarsimp simp: a_type_def split: if_splits)+
  done

lemma sc_at_typ2:
 "sc_at = obj_at (\<lambda>ko. \<exists>n. a_type ko = (ASchedContext n))"
  apply (rule obj_at_eq_helper)
  apply (auto simp add: is_sc_obj_def a_type_def
            split: kernel_object.splits)
  done

lemma reply_at_typ:
  "reply_at = typ_at AReply"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_reply_def a_type_def
            split: kernel_object.splits)
  done

lemma length_set_helper:
  "({x :: 'a list. length x = l} = {x. length x = l'}) = (l = l')"
  apply (rule iffI, simp_all)
  apply (cases "replicate l undefined \<in> {x :: 'a list. length x = l}")
   apply simp
  apply (subst(asm) mem_simps)
  apply simp
  done

lemma cap_table_at_typ:
  "cap_table_at n = typ_at (ACapTable n)"
  apply (rule obj_at_eq_helper)
  apply (case_tac obj, simp_all add: is_cap_table_def a_type_def
                                     well_formed_cnode_n_def)
  apply (auto simp: length_set_helper)
  done

lemma cte_at_def:
  "cte_at p s \<equiv> \<exists>cap. fst (get_cap p s) = {(cap,s)}"
  by (simp add: cte_wp_at_def)

lemma valid_cap_def2:
  "s \<turnstile> c \<equiv> cap_aligned c \<and> wellformed_cap c \<and> valid_cap_ref c s"
  apply (rule eq_reflection)
  apply (cases c)
          apply (simp_all add: valid_cap_simps wellformed_cap_simps
                               valid_cap_ref_simps
                        split: option.splits)
    apply (fastforce+)[5]
  by (simp add: valid_arch_cap_def2)

lemma valid_capsD:
  "\<lbrakk>caps_of_state s p = Some cap; valid_caps (caps_of_state s) s\<rbrakk>
   \<Longrightarrow> valid_cap cap s"
  by (cases p, simp add: valid_caps_def)

lemma tcb_cnode_index_distinct[simp]:
  "(tcb_cnode_index n = tcb_cnode_index m)
       = ((of_nat n :: 3 word) = (of_nat m :: 3 word))"
  by (simp add: tcb_cnode_index_def)


lemma tcb_cap_cases_simps[simp]:
  "tcb_cap_cases (tcb_cnode_index 0) =
   Some (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index (Suc 0)) =
   Some (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index 2) =
   Some (tcb_ipcframe, tcb_ipcframe_update,
         (\<lambda>_ _. is_nondevice_page_cap or (op = cap.NullCap)))"
  "tcb_cap_cases (tcb_cnode_index 3) =
   Some (tcb_fault_handler, tcb_fault_handler_update,
         (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index 4) =
   Some (tcb_timeout_handler, tcb_timeout_handler_update,
         (\<lambda>_ _. \<top>))"
  by (simp add: tcb_cap_cases_def)+

lemma ran_tcb_cap_cases:
  "ran (tcb_cap_cases) =
    {(tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>)),
     (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>)),
     (tcb_ipcframe, tcb_ipcframe_update, (\<lambda>_ _. is_nondevice_page_cap or (op = NullCap))),
     (tcb_fault_handler, tcb_fault_handler_update, (\<lambda>_ _. \<top>)),
     (tcb_timeout_handler, tcb_timeout_handler_update, (\<lambda>_ _. \<top>))}"
  by (simp add: tcb_cap_cases_def insert_commute)

lemma tcb_cnode_map_tcb_cap_cases:
  "tcb_cnode_map tcb = (\<lambda>bl. map_option (\<lambda>x. fst x tcb) (tcb_cap_cases bl))"
  by (rule ext) (simp add: tcb_cnode_map_def tcb_cap_cases_def)

lemma ran_tcb_cnode_map:
  "ran (tcb_cnode_map t) =
   {tcb_vtable t, tcb_ctable t, tcb_ipcframe t, tcb_fault_handler t, tcb_timeout_handler t}"
  by (fastforce simp: tcb_cnode_map_def)

lemma st_tcb_idle_cap_valid_Null [simp]:
  "st_tcb_at (idle or inactive) (fst sl) s \<longrightarrow>
   tcb_cap_valid NullCap sl s"
  by (fastforce simp: tcb_cap_valid_def tcb_cap_cases_def
                      pred_tcb_at_def obj_at_def
                      valid_ipc_buffer_cap_null)


lemma valid_objsI [intro]:
  "(\<And>obj x. kheap s x = Some obj \<Longrightarrow> valid_obj x obj s) \<Longrightarrow> valid_objs s"
  unfolding valid_objs_def by auto

lemma valid_objsE [elim]:
  "\<lbrakk> valid_objs s; kheap s x = Some obj; valid_obj x obj s \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding valid_objs_def by (auto simp: dom_def)


lemma obj_at_ko_at:
  "obj_at P p s \<Longrightarrow> \<exists>ko. ko_at ko p s \<and> P ko"
  by (auto simp add: obj_at_def)

lemma tcb_st_refs_of_simps[simp]:
 "tcb_st_refs_of (Running)               = {}"
 "tcb_st_refs_of (Inactive)              = {}"
 "tcb_st_refs_of (Restart)               = {}"
(* "tcb_st_refs_of (YieldTo t)             = {(t, TCBYieldTo)}"*)
 "tcb_st_refs_of (BlockedOnReply r)      = (if bound r then {(the r, TCBReply)} else {})"
 "tcb_st_refs_of (IdleThreadState)       = {}"
 "\<And>x. tcb_st_refs_of (BlockedOnReceive x r)  = (if bound r then {(x, TCBBlockedRecv), (the r, TCBReply)} else {(x, TCBBlockedRecv)})"
 "\<And>x. tcb_st_refs_of (BlockedOnSend x payl)  = {(x, TCBBlockedSend)}"
 "\<And>x. tcb_st_refs_of (BlockedOnNotification x) = {(x, TCBSignal)}"
  by (auto simp: tcb_st_refs_of_def)

lemma ep_q_refs_of_simps[simp]:
 "ep_q_refs_of  IdleEP    = {}"
 "\<And>q. ep_q_refs_of (RecvEP q) = set q \<times> {EPRecv}"
 "\<And>q. ep_q_refs_of (SendEP q) = set q \<times> {EPSend}"
  by (auto simp: ep_q_refs_of_def)

lemma ntfn_q_refs_of_simps[simp]:
 "ntfn_q_refs_of IdleNtfn        = {}"
 "ntfn_q_refs_of (WaitingNtfn q)   = set q \<times> {NTFNSignal}"
 "ntfn_q_refs_of (ActiveNtfn b)  = {}"
  by (auto simp: ntfn_q_refs_of_def)

lemma get_refs_simps[simp]:
  "get_refs RFFTYP (Some t) = {(t, RFFTYP)}"
  "get_refs RFFTYP None = {}"
  by (auto simp: get_refs_def)

lemma get_refs_def2:
  "get_refs REFTYP a = set_option a \<times> {REFTYP}"
by (simp add: get_refs_def split: option.splits)

lemma refs_of_simps[simp]:
 "refs_of (CNode sz cs)       = {}"
 "refs_of (TCB tcb)           = tcb_st_refs_of (tcb_state tcb)
                                \<union> get_refs TCBBound (tcb_bound_notification tcb)
                                \<union> get_refs TCBSchedContext (tcb_sched_context tcb)
                                \<union> get_refs TCBYieldTo (tcb_yield_to tcb)"
 "refs_of (Endpoint ep)       = ep_q_refs_of ep"
 "refs_of (Notification ntfn) = ntfn_q_refs_of (ntfn_obj ntfn)
                                \<union> get_refs NTFNBound (ntfn_bound_tcb ntfn)
                                \<union> get_refs NTFNSchedContext (ntfn_sc ntfn)"
 "refs_of (SchedContext sc n)   = get_refs SCNtfn (sc_ntfn sc)
                                \<union> get_refs SCTcb (sc_tcb sc)
                                \<union> get_refs SCYieldFrom (sc_yield_from sc)
                                \<union> set (map (\<lambda>r. (r, SCReply)) (sc_replies sc))"
 "refs_of (Reply r)           = get_refs ReplySchedContext (reply_sc r)
                                \<union> get_refs ReplyTCB (reply_tcb r)"
 "refs_of (ArchObj ao)        = {}"
  by (auto simp: refs_of_def)


lemma refs_of_rev:
 "(x, TCBBlockedRecv) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (\<exists>r. tcb_state tcb = BlockedOnReceive x r))"
 "(x, TCBBlockedSend) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (\<exists>pl. tcb_state tcb = BlockedOnSend    x pl))"
 "(x, TCBSignal) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_state tcb = BlockedOnNotification x))"
 "(x, EPRecv) \<in> refs_of ko =
    (\<exists>ep. ko = Endpoint ep \<and> (\<exists>q. ep = RecvEP q \<and> x \<in> set q))"
 "(x, EPSend) \<in> refs_of ko =
    (\<exists>ep. ko = Endpoint ep \<and> (\<exists>q. ep = SendEP q \<and> x \<in> set q))"
 "(x, NTFNSignal) \<in> refs_of ko =
    (\<exists>ntfn. ko = Notification ntfn \<and> (\<exists>q. ntfn_obj ntfn = WaitingNtfn q \<and> x \<in> set q))"
 "(x, TCBBound) \<in>  refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_bound_notification tcb = Some x))"
 "(x, NTFNBound) \<in> refs_of ko =
    (\<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = Some x))"
 "(x, TCBSchedContext) \<in>  refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_sched_context tcb = Some x))"
 "(x, TCBYieldTo) \<in>  refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_yield_to tcb = Some x))"
 "(x, NTFNSchedContext) \<in> refs_of ko =
    (\<exists>ntfn. ko = Notification ntfn \<and> (ntfn_sc ntfn = Some x))"
 "(x, TCBReply) \<in>  refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_state tcb = BlockedOnReply (Some x) \<or> (\<exists>n. tcb_state tcb = BlockedOnReceive n (Some x))))"
 "(x, SCTcb) \<in>  refs_of ko =
    (\<exists>sc n. ko = SchedContext sc n \<and> (sc_tcb sc = Some x))"
 "(x, SCNtfn) \<in>  refs_of ko =
    (\<exists>sc n. ko = SchedContext sc n \<and> (sc_ntfn sc = Some x))"
 "(x, SCReply) \<in>  refs_of ko =
    (\<exists>sc n. ko = SchedContext sc n \<and> (x \<in> set (sc_replies sc)))"
 "(x, ReplyTCB) \<in>  refs_of ko =
    (\<exists>reply. ko = Reply reply \<and> (reply_tcb reply = Some x))"
 "(x, ReplySchedContext) \<in>  refs_of ko =
    (\<exists>reply. ko = Reply reply \<and> (reply_sc reply = Some x))"
 "(x, SCYieldFrom) \<in>  refs_of ko =
    (\<exists>sc n. ko = SchedContext sc n \<and> (sc_yield_from sc = Some x))"
   by (auto simp:  refs_of_def
                     tcb_st_refs_of_def
                     ep_q_refs_of_def
                     ntfn_q_refs_of_def
                     get_refs_def
              split: kernel_object.splits
                     thread_state.splits
                     endpoint.splits
                     ntfn.splits
                     option.split)

lemma st_tcb_at_refs_of_rev:
  "obj_at (\<lambda>ko. (x, TCBBlockedRecv) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. \<exists>r. ts = BlockedOnReceive x r) t s"
  "obj_at (\<lambda>ko. (x, TCBBlockedRecv) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. \<exists>r. ts = BlockedOnReceive x r) t s"
  "obj_at (\<lambda>ko. (x, TCBReply) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. ts = BlockedOnReply (Some x) \<or> (\<exists>n. ts = BlockedOnReceive n (Some x))) t s"
  "obj_at (\<lambda>ko. (x, TCBBlockedSend) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. \<exists>pl. ts = BlockedOnSend x pl   ) t s"
  "obj_at (\<lambda>ko. (x, TCBSignal) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts.      ts = BlockedOnNotification x) t s"
(*  "obj_at (\<lambda>ko. (x, TCBYieldTo) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts.      ts = YieldTo x) t s"*)
  by (auto simp add: refs_of_rev pred_tcb_at_def)


lemma state_refs_of_elemD:
  "\<lbrakk> ref \<in> state_refs_of s x \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. ref \<in> refs_of obj) x s"
  by (clarsimp simp add: state_refs_of_def obj_at_def
                  split: option.splits)

lemma state_refs_of_eqD:
  "\<lbrakk> state_refs_of s x = S; S \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. refs_of obj = S) x s"
  by (clarsimp simp add: state_refs_of_def obj_at_def
                  split: option.splits)

lemma obj_at_state_refs_ofD:
  "obj_at P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_refs_of s p = refs_of ko"
  apply (clarsimp simp: obj_at_def state_refs_of_def)
  apply fastforce
  done

lemma ko_at_state_refs_ofD:
  "ko_at ko p s \<Longrightarrow> state_refs_of s p = refs_of ko"
  by (clarsimp dest!: obj_at_state_refs_ofD)


definition
  "tcb_ntfn_is_bound ntfn ko = (case ko of TCB tcb \<Rightarrow> tcb_bound_notification tcb = ntfn | _ \<Rightarrow> False)"

definition
  "tcb_sc_is_bound sc ko = (case ko of TCB tcb \<Rightarrow> tcb_sched_context tcb = sc | _ \<Rightarrow> False)"

definition
  "tcb_yield_to_is_bound yt ko = (case ko of TCB tcb \<Rightarrow> tcb_yield_to tcb = yt | _ \<Rightarrow> False)"

lemma st_tcb_at_state_refs_ofD:
  "st_tcb_at P t s \<Longrightarrow> \<exists>ts ntfnptr scptr1 ytptr. P ts
          \<and> obj_at (tcb_ntfn_is_bound ntfnptr) t s \<and> obj_at (tcb_sc_is_bound scptr1) t s
          \<and> obj_at (tcb_yield_to_is_bound ytptr) t s
          \<and> state_refs_of s t
     = (tcb_st_refs_of ts \<union> get_refs TCBBound ntfnptr \<union> get_refs TCBSchedContext scptr1
         \<union> get_refs TCBYieldTo ytptr)"
  by (auto simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def tcb_sc_is_bound_def
                 tcb_yield_to_is_bound_def state_refs_of_def)

lemma bound_tcb_at_state_refs_ofD:
  "bound_tcb_at P t s \<Longrightarrow> \<exists>ts ntfnptr scptr1 ytptr. P ntfnptr
          \<and> obj_at (tcb_ntfn_is_bound ntfnptr) t s \<and> obj_at (tcb_sc_is_bound scptr1) t s
          \<and> obj_at (tcb_yield_to_is_bound ytptr) t s
          \<and> state_refs_of s t = (tcb_st_refs_of ts \<union> get_refs TCBBound ntfnptr
         \<union> get_refs TCBSchedContext scptr1 \<union> get_refs TCBYieldTo ytptr)"
  by (auto simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def tcb_sc_is_bound_def
                 tcb_yield_to_is_bound_def state_refs_of_def)
(* do we need other versions? *)

lemma sym_refs_obj_atD:
  "\<lbrakk> obj_at P p s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     \<exists>ko. P ko \<and> state_refs_of s p = refs_of ko \<and>
        (\<forall>(x, tp)\<in>refs_of ko. obj_at (\<lambda>ko. (p, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule obj_at_state_refs_ofD)
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule(1) sym_refsD)
  apply (erule state_refs_of_elemD)
  done

lemma sym_refs_ko_atD:
  "\<lbrakk> ko_at ko p s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     state_refs_of s p = refs_of ko \<and>
     (\<forall>(x, tp)\<in>refs_of ko.  obj_at (\<lambda>ko. (p, symreftype tp) \<in> refs_of ko) x s)"
  by (drule(1) sym_refs_obj_atD, simp)

lemma sym_refs_st_tcb_atD: (* RT: other versions? *)
  "\<lbrakk> st_tcb_at P t s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     \<exists>ts ntfn scptr1 ytptr. P ts \<and> obj_at (tcb_ntfn_is_bound ntfn) t s
        \<and> obj_at (tcb_sc_is_bound scptr1) t s
        \<and> obj_at (tcb_yield_to_is_bound ytptr) t s
        \<and> state_refs_of s t = tcb_st_refs_of ts \<union> get_refs TCBBound ntfn
         \<union> get_refs TCBSchedContext scptr1 \<union> get_refs TCBYieldTo ytptr
        \<and> (\<forall>(x, tp)\<in>tcb_st_refs_of ts \<union> get_refs TCBBound ntfn
         \<union> get_refs TCBSchedContext scptr1 \<union> get_refs TCBYieldTo ytptr. obj_at (\<lambda>ko. (t, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule st_tcb_at_state_refs_ofD)
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply (rule_tac x=scptr1 in exI)
  apply (rule_tac x=ytptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD)
  apply (drule (1)sym_refs_obj_atD)
  apply auto
  done

lemma pspace_alignedE [elim]:
  "\<lbrakk> pspace_aligned s;
   x \<in> dom (kheap s); is_aligned x (obj_bits (the (kheap s x))) \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding pspace_aligned_def by auto

lemma ex_nonz_cap_toE:
  "\<lbrakk> ex_nonz_cap_to p s; \<And>cref. cte_wp_at (\<lambda>c. p \<in> zobj_refs c) cref s \<Longrightarrow> Q \<rbrakk>
    \<Longrightarrow> Q"
  by (fastforce simp: ex_nonz_cap_to_def)

lemma refs_of_live:
  "refs_of ko \<noteq> {} \<Longrightarrow> live ko"
  apply (cases ko, simp_all)
    apply (rename_tac tcb_ext)
     apply (case_tac "tcb_state tcb_ext", simp_all add: live_def)
    apply (fastforce simp: get_refs_def)+
  apply (rename_tac notification)
  apply (case_tac "ntfn_obj notification", simp_all add: live_ntfn_def)
   apply (fastforce simp: get_refs_def live_sc_def)+
  done

lemma hyp_refs_of_live:
  "hyp_refs_of ko \<noteq> {} \<Longrightarrow> live ko"
  by (cases ko, simp_all add: live_def hyp_refs_of_hyp_live)

lemma refs_of_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; refs_of ko = {} \<rbrakk> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> obj_at live p s"
  by (fastforce simp: obj_at_def intro!: refs_of_live)

lemma hyp_refs_of_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; hyp_refs_of ko = {}\<rbrakk> \<Longrightarrow> False  \<rbrakk> \<Longrightarrow> obj_at live p s"
  by (fastforce simp: obj_at_def intro!: hyp_refs_of_live)


lemma if_live_then_nonz_capD:
  assumes x: "if_live_then_nonz_cap s" "obj_at P p s"
  assumes y: "\<And>obj. \<lbrakk> P obj; kheap s p = Some obj \<rbrakk> \<Longrightarrow> live obj"
  shows "ex_nonz_cap_to p s" using x
  apply (clarsimp simp: if_live_then_nonz_cap_def)
  apply (erule allE[where x=p])
  apply (fastforce simp: obj_at_def dest!: y)
  done

lemma if_live_then_nonz_capD2:
  "\<lbrakk> if_live_then_nonz_cap s; kheap s p = Some obj;
     live obj \<rbrakk> \<Longrightarrow> ex_nonz_cap_to p s"
  apply (subgoal_tac "ko_at obj p s")
   apply (erule(1) if_live_then_nonz_capD)
   apply simp
  apply (simp add: obj_at_def)
  done

lemma caps_of_state_cte_wp_at:
 "caps_of_state s = (\<lambda>p. if (\<exists>cap. cte_wp_at (op = cap) p s)
                         then Some (THE cap. cte_wp_at (op = cap) p s)
                         else None)"
  by (rule ext) (clarsimp simp: cte_wp_at_def caps_of_state_def)

lemma cte_wp_at_caps_of_state:
 "cte_wp_at P p s = (\<exists>cap. caps_of_state s p = Some cap \<and> P cap)"
  by (clarsimp simp add: cte_wp_at_def caps_of_state_def)

lemmas ex_cte_cap_to_def =
  ex_cte_cap_wp_to_def[where P="\<top>", simplified simp_thms]

lemma ex_cte_cap_wp_to_weakenE:
  "\<lbrakk> ex_cte_cap_wp_to P p s;
      \<And>cte_cap. \<lbrakk> P cte_cap; p \<in> cte_refs cte_cap (interrupt_irq_node s) \<rbrakk> \<Longrightarrow> Q cte_cap \<rbrakk>
       \<Longrightarrow> ex_cte_cap_wp_to Q p s"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (elim exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma if_unsafe_then_capD:
  "\<lbrakk> cte_wp_at P p s; if_unsafe_then_cap s; \<And>cap. P cap \<Longrightarrow> cap \<noteq> NullCap \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to (\<lambda>cap. \<exists>cap'. P cap' \<and> appropriate_cte_cap cap' cap) p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (unfold if_unsafe_then_cap_def)
  apply (elim allE, drule(1) mp)
  apply (auto elim!: ex_cte_cap_wp_to_weakenE)
  done

lemma zombies_finalD:
  "\<lbrakk> cte_wp_at P p s; zombies_final s; \<And>cap. P cap \<Longrightarrow> is_zombie cap \<rbrakk>
     \<Longrightarrow> cte_wp_at (\<lambda>cap. is_final_cap' cap s) p s"
  unfolding zombies_final_def
  apply (drule spec, erule mp)
  apply (clarsimp simp: cte_wp_at_def)
  done


lemma physical_valid_cap_not_empty_range:
  "\<lbrakk>valid_cap cap s; cap_class cap = PhysicalClass\<rbrakk> \<Longrightarrow> cap_range cap \<noteq> {}"
  apply (case_tac cap)
   apply (simp_all add:cap_range_def valid_cap_simps cap_aligned_def is_aligned_no_overflow)
  apply (rename_tac arch_cap)
  apply (clarsimp simp: physical_arch_cap_has_ref)
  done

lemma valid_ioc_def2:
  "valid_ioc s \<equiv>
   \<forall>p. is_original_cap s p \<longrightarrow> null_filter (caps_of_state s) p \<noteq> None"
  apply (rule eq_reflection)
  apply (clarsimp simp add: valid_ioc_def)
  apply (intro iff_allI weak_imp_cong refl)
  apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma has_reply_cap_cte_wpD:
  "\<And>t sl. cte_wp_at (op = (ReplyCap t)) sl s \<Longrightarrow> has_reply_cap t s"
  by (fastforce simp: has_reply_cap_def)

lemma mdb_cte_atD:
  "\<lbrakk> m c = Some p; mdb_cte_at ct_at m \<rbrakk>
     \<Longrightarrow> ct_at p \<and> ct_at c"
  by (simp add: mdb_cte_at_def)

lemma zobj_refs_to_obj_refs:
  "(x \<in> zobj_refs cap) = (x \<in> obj_refs cap \<and> \<not> is_zombie cap)"
  by (cases cap, simp_all add: is_zombie_def)

lemma idle_only_sc_refs:
  "valid_idle s \<Longrightarrow> state_refs_of s (idle_thread s) = {(idle_sc_ptr, TCBSchedContext)}"
  apply (clarsimp simp: valid_idle_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def
                        tcb_yield_to_is_bound_def state_refs_of_def)
  done

lemma idle_not_queued:
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s);
   state_refs_of s ptr = queue \<times> {rt}; idle_thread s \<in> queue\<rbrakk> \<Longrightarrow>
   ptr = idle_sc_ptr"
  by (frule idle_only_sc_refs, fastforce simp: valid_idle_def sym_refs_def)

lemma idle_not_queued':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s);
   state_refs_of s ptr = insert t queue \<times> {rt}; idle_thread s \<in> queue\<rbrakk> \<Longrightarrow>
   ptr = idle_sc_ptr"
  by (frule idle_only_sc_refs, fastforce simp: valid_idle_def sym_refs_def)

lemma mdb_cte_atI:
  "\<lbrakk> \<And>c p. m c = Some p \<Longrightarrow> ct_at p \<and> ct_at c \<rbrakk>
     \<Longrightarrow> mdb_cte_at ct_at m"
  by (simp add: mdb_cte_at_def)

lemma only_idleD:
  "\<lbrakk> st_tcb_at idle t s; only_idle s \<rbrakk> \<Longrightarrow> t = idle_thread s"
  by (simp add: only_idle_def)

lemma only_idleI:
  "(\<And>t. st_tcb_at idle t s \<Longrightarrow> t = idle_thread s) \<Longrightarrow> only_idle s"
  by (simp add: only_idle_def)

lemma valid_refs_def2:
  "valid_refs R = (\<lambda>s. \<forall>c \<in> ran (caps_of_state s). R \<inter> cap_range c = {})"
  apply (simp add: valid_refs_def cte_wp_at_caps_of_state ran_def)
  apply (rule ext, fastforce)
  done

lemma idle_no_ex_cap:
  "\<lbrakk>valid_global_refs s; valid_objs s\<rbrakk> \<Longrightarrow>
   \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (simp add: ex_nonz_cap_to_def valid_global_refs_def valid_refs_def2 cte_wp_at_caps_of_state
              del: split_paired_Ex split_paired_All)
  apply (intro allI notI impI)
  apply (drule bspec, blast)
  apply (clarsimp simp: cap_range_def zobj_refs_to_obj_refs)
  by blast

lemma caps_of_state_cteD:
  "caps_of_state s p = Some cap \<Longrightarrow> cte_wp_at (op = cap) p s"
  by (simp add: cte_wp_at_caps_of_state)

lemma untyped_mdb_alt:
  "untyped_mdb (cdt s) (caps_of_state s) = untyped_children_in_mdb s"
  apply (simp add: untyped_children_in_mdb_def untyped_mdb_def cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma untyped_children_in_mdbE:
  assumes x: "untyped_children_in_mdb s" "cte_wp_at (op = cap) ptr s"
             "is_untyped_cap cap" "cte_wp_at P ptr' s"
  assumes y: "\<And>cap'. \<lbrakk> cte_wp_at (op = cap') ptr' s; P cap' \<rbrakk> \<Longrightarrow>
                 obj_refs cap' \<inter> untyped_range cap \<noteq> {}"
  assumes z: "ptr' \<in> descendants_of ptr (cdt s) \<Longrightarrow> Q"
  shows Q using x
  apply (clarsimp simp: untyped_children_in_mdb_def
                  simp del: split_paired_All split_paired_Ex)
  apply (erule allE[where x=ptr], erule allE[where x=ptr'], erule impE)
   apply (rule exI, (erule conjI)+)
   apply (clarsimp simp: cte_wp_at_def y)
  apply (erule z)
  done

lemma cte_wp_at_cases:
  "cte_wp_at P t s = ((\<exists>sz fun cap. kheap s (fst t) = Some (CNode sz fun) \<and>
                                    well_formed_cnode_n sz fun \<and>
                                    fun (snd t) = Some cap \<and> P cap) \<or>
                      (\<exists>tcb get set restr. kheap s (fst t) = Some (TCB tcb) \<and>
                             tcb_cap_cases (snd t) = Some (get, set, restr) \<and>
                             P (get tcb)))"
  apply (cases t)
  apply (cases "kheap s (fst t)")
   apply (simp add: cte_wp_at_def get_cap_def
                    get_object_def gets_def get_def return_def assert_def
                    fail_def bind_def)
  apply (simp add: cte_wp_at_def get_cap_def tcb_cnode_map_def bind_def
                   get_object_def assert_opt_def return_def gets_def get_def
                   assert_def fail_def dom_def
              split: if_split_asm kernel_object.splits
                     option.splits)
  apply (simp add: tcb_cap_cases_def)
  done

lemma cte_wp_at_cases2:
  "cte_wp_at P t s =
   ((\<exists>sz fun cap. kheap s (fst t) = Some (CNode sz fun) \<and>
                  well_formed_cnode_n sz fun \<and> fun (snd t) = Some cap \<and> P cap) \<or>
    (\<exists>tcb cap. kheap s (fst t) = Some (TCB tcb) \<and>
               (tcb_cnode_map tcb (snd t) = Some cap \<and> P cap)))"
  by (auto simp add: cte_wp_at_cases tcb_cap_cases_def tcb_cnode_map_def)

lemma cte_wp_at_pspaceI:
  "\<lbrakk> cte_wp_at P slot s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> cte_wp_at P slot s'"
  by (simp add: cte_wp_at_cases)

context Arch begin
lemma valid_arch_cap_pspaceI:
  "\<lbrakk> valid_arch_cap acap s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_arch_cap acap s'"
  unfolding valid_arch_cap_def
  by (auto intro: obj_at_pspaceI split: arch_cap.split)
end

context begin interpretation Arch .
requalify_facts
  valid_arch_cap_pspaceI
end

lemma valid_cap_pspaceI:
  "\<lbrakk> s \<turnstile> cap; kheap s = kheap s' \<rbrakk> \<Longrightarrow> s' \<turnstile> cap"
  unfolding valid_cap_def
  apply (cases cap)
  by (auto intro: obj_at_pspaceI cte_wp_at_pspaceI valid_arch_cap_pspaceI
            simp: obj_range_def valid_untyped_def pred_tcb_at_def
           split: option.split sum.split)


(* FIXME-NTFN: ugly proof *)
lemma valid_obj_pspaceI:
  "\<lbrakk> valid_obj ptr obj s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_obj ptr obj s'"
  unfolding valid_obj_def
  apply (cases obj)
      by (auto simp add: valid_ntfn_def valid_cs_def valid_tcb_def valid_ep_def
                            valid_tcb_state_def pred_tcb_at_def valid_bound_obj_def
                            wellformed_arch_pspace valid_sched_context_def valid_reply_def obj_at_def
                 intro: obj_at_pspaceI valid_cap_pspaceI valid_arch_tcb_pspaceI
                 split: ntfn.splits endpoint.splits list.splits
                        thread_state.splits option.split
          | auto split: kernel_object.split)+

lemma valid_objs_pspaceI:
  "\<lbrakk> valid_objs s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_objs s'"
  unfolding valid_objs_def
  by (auto intro: valid_obj_pspaceI dest!: bspec [OF _ domI])

lemma state_refs_of_pspaceI:
  "\<lbrakk> P (state_refs_of s); kheap s = kheap s' \<rbrakk> \<Longrightarrow> P (state_refs_of s')"
  unfolding state_refs_of_def
  by simp

lemma distinct_pspaceI:
  "pspace_distinct s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> pspace_distinct s'"
  by (simp add: pspace_distinct_def)

lemma iflive_pspaceI:
  "if_live_then_nonz_cap s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> if_live_then_nonz_cap s'"
  unfolding if_live_then_nonz_cap_def ex_nonz_cap_to_def
  by (fastforce simp: obj_at_def intro: cte_wp_at_pspaceI)

lemma cte_wp_at_pspace:
  "kheap s = kheap s' \<Longrightarrow> cte_wp_at P p s = cte_wp_at P p s'"
  by (fastforce elim!: cte_wp_at_pspaceI)

lemma caps_of_state_pspace:
  assumes x: "kheap s = kheap s'"
  shows      "caps_of_state s = caps_of_state s'"
  by (simp add: caps_of_state_cte_wp_at cte_wp_at_pspace [OF x] cong: if_cong)

lemma ifunsafe_pspaceI:
  "if_unsafe_then_cap s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> interrupt_irq_node s = interrupt_irq_node s'
       \<Longrightarrow> if_unsafe_then_cap s'"
  unfolding if_unsafe_then_cap_def ex_cte_cap_wp_to_def
  apply (frule caps_of_state_pspace)
  by (auto simp: cte_wp_at_cases)

lemma valid_idle_pspaceI:
  "valid_idle s \<Longrightarrow> \<lbrakk>kheap s = kheap s'; idle_thread s = idle_thread s'\<rbrakk> \<Longrightarrow> valid_idle s'"
  unfolding valid_idle_def pred_tcb_at_def
  by (fastforce elim!: obj_at_pspaceI cte_wp_at_pspaceI)

lemma gen_obj_refs_Int:
  "(gen_obj_refs cap \<inter> gen_obj_refs cap' = {})
     = (obj_refs cap \<inter> obj_refs cap' = {}
            \<and> cap_irqs cap \<inter> cap_irqs cap' = {}
            \<and> arch_gen_refs cap \<inter> arch_gen_refs cap' = {})"
  by (simp add: gen_obj_refs_def Int_Un_distrib Int_Un_distrib2
                image_Int[symmetric] Int_image_empty image_Int[symmetric])

lemma is_final_cap'_def2:
  "is_final_cap' cap =
    (\<lambda>s. \<exists>cref. \<forall>cref'. cte_wp_at (\<lambda>c. gen_obj_refs cap \<inter> gen_obj_refs c \<noteq> {}) cref' s
                  = (cref' = cref))"
  apply (rule ext)
  apply (auto simp: is_final_cap'_def cte_wp_at_def
                    set_eq_iff)
  done

lemma zombies_final_pspaceI:
  assumes x: "zombies_final s"
      and y: "kheap s = kheap s'"
  shows      "zombies_final s'"
  using x unfolding zombies_final_def is_final_cap'_def2
  by (simp only: cte_wp_at_pspace [OF y])

lemma pspace_pspace_update:
  "kheap (kheap_update (\<lambda>a. ps) s) = ps" by simp

lemma valid_pspace_eqI:
  "\<lbrakk> valid_pspace s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_pspace s'"
  unfolding valid_pspace_def
  by (auto simp: pspace_aligned_def
           intro: valid_objs_pspaceI state_refs_of_pspaceI state_hyp_refs_of_pspaceI
                  distinct_pspaceI iflive_pspaceI
                  ifunsafe_pspaceI zombies_final_pspaceI)

lemma cte_wp_caps_of_lift:
  assumes c: "\<And>p P. cte_wp_at P p s = cte_wp_at P p s'"
  shows "caps_of_state s = caps_of_state s'"
  apply (rule ext)
  apply (case_tac "caps_of_state s' x")
   apply (rule classical)
   apply (clarsimp dest!: caps_of_state_cteD simp add: c)
   apply (simp add: cte_wp_at_caps_of_state)
  apply clarsimp
  apply (clarsimp dest!: caps_of_state_cteD simp add: c [symmetric])
  apply (simp add: cte_wp_at_caps_of_state)
  done

lemma ex_cte_cap_to_pres:
  assumes x: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  assumes irq: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  shows      "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> f \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (simp add: ex_cte_cap_wp_to_def,
      wp hoare_vcg_ex_lift hoare_use_eq[where f=interrupt_irq_node, OF irq, OF x])

lemma valid_mdb_eqI:
  assumes "valid_mdb s"
  assumes c: "\<And>p P. cte_wp_at P p s = cte_wp_at P p s'"
  assumes "cdt s = cdt s'"
  assumes "is_original_cap s = is_original_cap s'"
  shows "valid_mdb s'" using assms
  apply (simp add: valid_mdb_def)
   apply (rule conjI)
   apply (force simp add: valid_mdb_def swp_def mdb_cte_at_def)
  apply (clarsimp simp add: cte_wp_caps_of_lift [OF c])
  done

lemma set_object_at_obj:
  "\<lbrace> \<lambda>s. obj_at P p s \<and> (p = r \<longrightarrow> P obj) \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma set_object_at_obj1:
  "P obj \<Longrightarrow> \<lbrace> obj_at P p \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma set_object_at_obj2:
  "(\<And>ko. Q ko \<Longrightarrow> \<not>P ko) \<Longrightarrow>
  \<lbrace> obj_at P p and obj_at Q r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma test:
  "\<lbrace> ep_at p and tcb_at r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. ep_at p \<rbrace>"
  apply (rule set_object_at_obj2)
  apply (clarsimp simp: is_obj_defs)
  done

text {* Lemmas about well-formed states *}

lemma valid_pspaceI [intro]:
  "\<lbrakk> valid_objs s; pspace_aligned s; sym_refs (state_refs_of s); sym_refs (state_hyp_refs_of s);
     pspace_distinct s; if_live_then_nonz_cap s; zombies_final s \<rbrakk>
     \<Longrightarrow> valid_pspace s"
  unfolding valid_pspace_def by simp

lemma valid_pspaceE [elim?]:
  assumes vp: "valid_pspace s"
  and     rl: "\<lbrakk> valid_objs s; pspace_aligned s;
                 sym_refs (state_refs_of s);  sym_refs (state_hyp_refs_of s);
                 pspace_distinct s; if_live_then_nonz_cap s;
                 zombies_final s \<rbrakk> \<Longrightarrow> R"
  shows    R
  using vp
  unfolding valid_pspace_def by (auto intro: rl)

lemma valid_objs_valid_cs [dest?]:
  assumes vp: "valid_objs s"
  and    ran: "CNode sz ct \<in> ran (kheap s)"
  shows  "valid_cs sz ct s"
  using vp ran unfolding valid_objs_def
  by (auto simp: valid_obj_def ran_def dom_def)

lemma valid_pspace_valid_cs [dest?]:
  assumes vp: "valid_pspace s"
  and    ran: "CNode sz ct \<in> ran (kheap s)"
  shows  "valid_cs sz ct s"
  using vp
  by (rule valid_pspaceE)
     (simp add: valid_objs_valid_cs ran)

lemma valid_pspace_aligned:
  assumes vp: "valid_pspace s"
  and    lup: "kheap s addr = Some ko"
  shows  "is_aligned addr (obj_bits ko)"
  using vp
  apply (rule valid_pspaceE)
  apply (unfold pspace_aligned_def)
  apply (drule bspec [OF _ domI])
   apply (rule lup)
  apply (simp add: lup)
  done

lemma valid_pspace_valid_cs_size [intro?]:
  assumes ran: "CNode sz cs \<in> ran (kheap s)"
  and      vp: "valid_pspace s"
  shows  "valid_cs_size sz cs"
  using valid_pspace_valid_cs [OF vp ran]
  unfolding valid_cs_def ..

lemma valid_objs_valid_cs_size [intro?]:
  assumes ran: "CNode sz cs \<in> ran (kheap s)"
  and      vp: "valid_objs s"
  shows  "valid_cs_size sz cs"
  using valid_objs_valid_cs [OF vp ran]
  unfolding valid_cs_def ..

lemma valid_cs_size_objsI [intro?]:
  "\<lbrakk> valid_objs s; kheap s r = Some (CNode sz ps) \<rbrakk>
  \<Longrightarrow> valid_cs_size sz ps"
  by (drule ranI, erule valid_objs_valid_cs_size)

lemma valid_cs_sizeI [intro?]:
  "\<lbrakk> valid_pspace s; kheap s r = Some (CNode sz ps) \<rbrakk>
  \<Longrightarrow> valid_cs_size sz ps"
  by (drule ranI, erule valid_pspace_valid_cs_size)

lemma wf_cs_insert:
  "\<lbrakk> well_formed_cnode_n sz cs; cs ref \<noteq> None \<rbrakk> \<Longrightarrow> well_formed_cnode_n sz (cs (ref \<mapsto> val))"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (subst insert_absorb, simp_all)
  apply (drule domI, fastforce)
  done

lemma obj_bits_CNode:
  "\<lbrakk> valid_cs_size sz ps; ps cref = Some cap \<rbrakk> \<Longrightarrow>
  obj_bits (CNode sz ps) = cte_level_bits + length cref"
  by (auto simp: valid_cs_size_def well_formed_cnode_n_def)

lemma obj_bits_CNode':
  "\<lbrakk> valid_cs_size sz ps; cref \<in> dom ps \<rbrakk> \<Longrightarrow>
  obj_bits (CNode sz ps) = cte_level_bits + length cref"
  by (drule domD, erule exE, rule obj_bits_CNode)

lemma valid_cs_sizeE [elim]:
  assumes "valid_cs_size sz cs"
  and     "\<lbrakk> sz < word_bits - cte_level_bits; dom cs = {x. length x = sz};
            obj_bits (CNode sz cs) = cte_level_bits + sz\<rbrakk>
           \<Longrightarrow> R"
  shows "R"
  using assms
  by (auto simp: valid_cs_size_def well_formed_cnode_n_def)

lemma valid_objs_valid_sched_context [dest?]:
  assumes vp: "valid_objs s"
  and    ran: "SchedContext sc n \<in> ran (kheap s)"
  shows  "valid_sched_context sc s"
  using vp ran unfolding valid_objs_def
  by (auto simp: valid_obj_def ran_def dom_def)

lemma valid_objs_valid_sched_context_size [dest?]:
  assumes vp: "valid_objs s"
  and    ran: "SchedContext sc n \<in> ran (kheap s)"
  shows  "valid_sched_context_size n"
  using vp ran unfolding valid_objs_def
  by (auto simp: valid_obj_def ran_def dom_def)

lemma valid_pspace_valid_sched_context [dest?]:
  assumes vp: "valid_pspace s"
  and    ran: "SchedContext sc n \<in> ran (kheap s)"
  shows  "valid_sched_context sc s"
  using vp
  by (rule valid_pspaceE)
     (drule valid_objs_valid_sched_context, rule ran, simp)

lemma valid_pspace_valid_sched_context_size [intro?]:
  assumes ran: "SchedContext sc n \<in> ran (kheap s)"
  and      vp: "valid_pspace s"
  shows  "valid_sched_context_size n"
  using vp
  by (rule valid_pspaceE)
     (drule valid_objs_valid_sched_context_size, rule ran, simp)


lemma valid_sched_context_objsI [intro?]:
  "\<lbrakk> valid_objs s; kheap s r = Some (SchedContext sc n) \<rbrakk>
  \<Longrightarrow> valid_sched_context sc s"
  by (drule ranI, erule valid_objs_valid_sched_context)

lemma valid_sched_contextI [intro?]:
  "\<lbrakk> valid_pspace s; kheap s r = Some (SchedContext sc n) \<rbrakk>
  \<Longrightarrow> valid_sched_context sc s"
  by (drule ranI, erule valid_pspace_valid_sched_context)

lemma valid_sched_context_size_objsI [intro?]:
  "\<lbrakk> valid_objs s; kheap s r = Some (SchedContext sc n) \<rbrakk>
  \<Longrightarrow> valid_sched_context_size n"
  by (drule ranI, erule valid_objs_valid_sched_context_size)

lemma valid_sched_context_sizeI [intro?]:
  "\<lbrakk> valid_pspace s; kheap s r = Some (SchedContext sc n) \<rbrakk>
  \<Longrightarrow> valid_sched_context_size n"
  by (drule ranI, erule valid_pspace_valid_sched_context_size)

lemma valid_obj_sizes:
  assumes vp: "valid_objs s"
  and     ko: "ko \<in> ran (kheap s)"
  shows   "obj_bits ko < word_bits"
proof (cases ko)
  case CNode
  thus ?thesis using vp ko
    by (auto dest!: valid_objs_valid_cs_size)
next
  case SchedContext
  thus ?thesis using vp ko
     by (auto dest!: valid_objs_valid_sched_context_size valid_sc_size_less_word_bits)
next
  case (ArchObj ako)
  show ?thesis using ArchObj by (simp only: valid_arch_sizes)
qed (auto elim: valid_pspaceE
          simp: valid_arch_sizes[unfolded word_bits_conv] word_bits_conv)

lemma valid_pspace_obj_sizes:
  assumes vp: "valid_pspace s"
  and     ko: "ko \<in> ran (kheap s)"
  shows   "obj_bits ko < word_bits" using assms
  by - (rule valid_obj_sizes, auto simp: valid_pspace_def)

lemma valid_objs_replicate:
  assumes aligned: "pspace_aligned s"
  assumes valid: "valid_objs s"
  and     dom:   "x \<in> dom (kheap s)"
  shows   "to_bl x = (take (word_bits - (obj_bits (the (kheap s x)))) (to_bl x)) @
                     replicate (obj_bits (the (kheap s x))) False"
proof -
  let ?a = "obj_bits (the (kheap s x))"

  from aligned have "is_aligned x ?a" using dom
    unfolding pspace_aligned_def ..

  thus ?thesis
    proof (rule is_aligned_replicate[where 'a=machine_word_len, folded word_bits_def])
  show "obj_bits (the (kheap s x)) \<le> word_bits"
    by (rule order_less_imp_le, rule valid_obj_sizes [OF _ dom_ran]) fact+
  qed
qed

lemma valid_pspace_replicate:
  assumes "valid_pspace s"
  and     "x \<in> dom (kheap s)"
  shows   "to_bl x = (take (word_bits - (obj_bits (the (kheap s x)))) (to_bl x)) @
                     replicate (obj_bits (the (kheap s x))) False"
  using assms
  by - (rule valid_objs_replicate, auto simp: valid_pspace_def)

lemma valid_objs_captable_dom_length:
  assumes "valid_objs s"
  assumes "CNode sz ct \<in> ran (kheap s)"
  assumes ct: "ct y \<noteq> None"
  shows "length y < word_bits - cte_level_bits"
proof -
  have "valid_cs_size sz ct" by (rule valid_objs_valid_cs_size) fact+
  thus ?thesis using ct
    by (auto simp: valid_cs_size_def well_formed_cnode_n_def)
qed

lemma valid_pspace_captable_dom_length:
  assumes "valid_pspace s"
  and     "CNode sz ct \<in> ran (kheap s)"
  and     "ct y \<noteq> None"
  shows "length y < word_bits - cte_level_bits"
  using assms
  by - (rule valid_objs_captable_dom_length, auto simp: valid_pspace_def)

lemma valid_objs_replicate':
  assumes valid: "valid_objs s"
  and   aligned: "pspace_aligned s"
  and     dom:   "x \<in> dom (kheap s)"
  and      l1:   "l1 = word_bits - (obj_bits (the (kheap s x)))"
  and      l2:   "l2 = (obj_bits (the (kheap s x)))"
  and      yv:   "y = (to_bl x)"
  shows   "to_bl x = (take l1 y) @ replicate l2 False"
  by ((subst l1 l2 yv)+, rule valid_objs_replicate) fact+

lemma valid_pspace_replicate':
  assumes valid: "valid_pspace s"
  and     dom:   "x \<in> dom (kheap s)"
  and      l1:   "l1 = word_bits - (obj_bits (the (kheap s x)))"
  and      l2:   "l2 = (obj_bits (the (kheap s x)))"
  and      yv:   "y = (to_bl x)"
  shows   "to_bl x = (take l1 y) @ replicate l2 False"
  by ((subst l1 l2 yv)+, rule valid_pspace_replicate) fact+

lemma pspace_replicate_dom:
  assumes "valid_pspace s"
  and pv: "kheap s (of_bl x) = Some (CNode sz ct)"
  shows   "replicate (obj_bits (CNode sz ct) - cte_level_bits) False \<in> dom ct"
proof -
  have "valid_cs_size sz ct"
    by (rule valid_cs_sizeI) fact+

  thus ?thesis
    by (rule valid_cs_sizeE) simp
qed

lemma obj_at_valid_objsE:
  "\<lbrakk> obj_at P p s; valid_objs s;
    \<And>ko. \<lbrakk> kheap s p = Some ko; P ko; valid_obj p ko s \<rbrakk> \<Longrightarrow> Q
  \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: valid_objs_def obj_at_def dom_def)

lemma valid_CNodeCapE:
  assumes p: "s \<turnstile> CNodeCap ptr cbits guard" "valid_objs s" "pspace_aligned s"
  assumes R: "\<And>cs. \<lbrakk> 0 < cbits; kheap s ptr = Some (CNode cbits cs);
               \<forall>cap\<in>ran cs. s \<turnstile> cap; dom cs = {x. length x = cbits};
               is_aligned ptr (cte_level_bits + cbits); cbits < word_bits - cte_level_bits
              \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p
  apply (clarsimp simp: pspace_aligned_def valid_cap_def)
  apply (erule (1) obj_at_valid_objsE)
  apply (drule bspec, blast)
  apply (clarsimp simp add: is_cap_table)
  apply (clarsimp simp: valid_obj_def valid_cs_def well_formed_cnode_n_def)
  apply (erule valid_cs_sizeE)
  apply (clarsimp simp: cap_aligned_def)
  apply (erule (5) R)
  done

lemma cap_table_at_cte_at:
  "\<lbrakk> cap_table_at cbits ptr s; length offset = cbits \<rbrakk>
  \<Longrightarrow> cte_at (ptr, offset) s"
  apply (clarsimp simp: obj_at_def cte_wp_at_cases is_cap_table
                        well_formed_cnode_n_def length_set_helper)
  apply (rule domD, simp)
  done

declare map_nth_0 [simp del]

lemma valid_cs_sizeE2:
  assumes v: "valid_cs_size sz cs"
  assumes c: "cref \<in> dom cs"
  assumes R: "\<lbrakk>length cref \<le> word_bits - cte_level_bits;
               dom cs = {x. length x = length cref};
               obj_bits (CNode sz cs) = cte_level_bits + length cref\<rbrakk> \<Longrightarrow> R"
  shows "R"
proof -
  from v have sz:
    "sz < word_bits - cte_level_bits"
    "dom cs = {x. length x = sz}"
    "obj_bits (CNode sz cs) = cte_level_bits + sz"
    by auto
  with c
  have "sz = length cref" by auto
  with sz
  show ?thesis
    by - (rule R, auto)
qed

lemma pred_tcb_weakenE:
  "\<lbrakk> pred_tcb_at proj P t s; \<And>tcb . P (proj tcb) \<Longrightarrow> P' (proj tcb) \<rbrakk> \<Longrightarrow> pred_tcb_at proj P' t s"
  by (auto simp: pred_tcb_at_def elim: obj_at_weakenE)

lemma pred_tcb_at_pure:
  "pred_tcb_at g (\<lambda>a. P) (f s) s = (tcb_at (f s) s \<and> P)"
  unfolding pred_tcb_at_def
  apply (clarsimp simp add: obj_at_def)
  apply (rule iffI)
   apply clarsimp
   apply (auto simp: is_tcb_def split: kernel_object.splits)[1]
  apply clarsimp
  apply (case_tac ko; simp_all)
     apply (auto simp: is_tcb_def split: kernel_object.splits)
  done

(* sseefried:
     This lemma exists only to make existing proofs go through more easily.
     Replacing 'st_tcb_at_weakenE' with 'pred_tcb_at_weakenE' in a proof
     should yield the same result.
*)
lemma st_tcb_weakenE:
  "\<lbrakk> st_tcb_at P t s; \<And>st . P st \<Longrightarrow> P' st \<rbrakk> \<Longrightarrow> st_tcb_at P' t s"
  by (auto simp: pred_tcb_weakenE)

lemma tcb_at_st_tcb_at:
  "tcb_at = st_tcb_at (\<lambda>_. True)"
  apply (rule ext)+
  apply (simp add: tcb_at_def pred_tcb_at_def obj_at_def is_tcb_def)
  apply (rule arg_cong [where f=Ex], rule ext)
  apply (case_tac ko, simp_all)
  done

lemma pred_tcb_at_tcb_at:
  "pred_tcb_at proj P t s \<Longrightarrow> tcb_at t s"
  by (auto simp: tcb_at_def pred_tcb_at_def obj_at_def is_tcb)

lemmas st_tcb_at_tcb_at = pred_tcb_at_tcb_at[where proj=itcb_state, simplified]

lemma st_tcb_at_opeqI:
  "\<lbrakk> st_tcb_at (op= st) t s ; test st \<rbrakk> \<Longrightarrow> st_tcb_at test t s"
  by (fastforce simp add: pred_tcb_def2)

lemma cte_wp_at_weakenE:
  "\<lbrakk> cte_wp_at P t s; \<And>c. P c \<Longrightarrow> P' c \<rbrakk> \<Longrightarrow> cte_wp_at P' t s"
  by (simp add: cte_wp_at_def) blast

lemma le_minus_minus:
  "\<lbrakk> a \<le> b - c; (c :: ('a :: len) word) \<le> b \<rbrakk> \<Longrightarrow> c \<le> b - a"
  by (simp add: word_le_nat_alt unat_sub)

lemma tcb_at_cte_at:
  "\<lbrakk> tcb_at t s; ref \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> cte_at (t, ref) s"
  by (clarsimp simp: obj_at_def cte_wp_at_cases is_tcb)

lemma cte_at_cases:
  "cte_at t s = ((\<exists>sz fun. kheap s (fst t) = Some (CNode sz fun) \<and>
                        well_formed_cnode_n sz fun \<and>
                        (snd t) \<in> dom fun) \<or>
                (\<exists>tcb. kheap s (fst t) = Some (TCB tcb) \<and>
                         (snd t \<in> dom tcb_cap_cases)))"
  by (auto simp add: cte_wp_at_cases dom_def)

lemma cte_atE [consumes 1, case_names CNode TCB, elim?]:
  assumes cat: "cte_at t s"
  and     rct: "\<And>sz fun. \<lbrakk>kheap s (fst t) = Some (CNode sz fun); snd t \<in> dom fun\<rbrakk> \<Longrightarrow> R"
  and    rtcb: "\<And>tcb. \<lbrakk>kheap s (fst t) = Some (TCB tcb); snd t \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using cat by (auto simp: cte_at_cases intro: rct rtcb)

lemma cte_wp_atE:
  "\<lbrakk>cte_wp_at P t s;
  \<And>sz fun cte. \<lbrakk>kheap s (fst t) = Some (CNode sz fun); well_formed_cnode_n sz fun;
                fun (snd t) = Some cte; P cte\<rbrakk> \<Longrightarrow> R;
  \<And>tcb getF setF restr. \<lbrakk>kheap s (fst t) = Some (TCB tcb);
                          tcb_cap_cases (snd t) = Some (getF, setF, restr); P (getF tcb) \<rbrakk> \<Longrightarrow> R \<rbrakk>
  \<Longrightarrow> R"
  by (fastforce simp: cte_wp_at_cases dom_def)

lemma cte_wp_at_cteI:
  "\<lbrakk>kheap s (fst t) = Some (CNode sz fun); well_formed_cnode_n sz fun; fun (snd t) = Some cte; P cte\<rbrakk>
  \<Longrightarrow> cte_wp_at P t s"
  by (auto simp: cte_wp_at_cases dom_def well_formed_cnode_n_def length_set_helper)

lemma cte_wp_at_tcbI:
  "\<lbrakk>kheap s (fst t) = Some (TCB tcb); tcb_cap_cases (snd t) = Some (getF, setF); P (getF tcb) \<rbrakk>
  \<Longrightarrow> cte_wp_at P t s"
  by (auto simp: cte_wp_at_cases dom_def)

lemma ko_at_obj_congD:
  "\<lbrakk> ko_at k1 p s; ko_at k2 p s \<rbrakk> \<Longrightarrow> k1 = k2"
  unfolding obj_at_def
  by simp

text {* using typ_at triples to prove other triples *}

lemma cte_at_typ:
  "cte_at p = (\<lambda>s. typ_at (ACapTable (length (snd p))) (fst p) s
                \<or> (typ_at ATCB (fst p) s \<and> snd p \<in> dom tcb_cap_cases))"
  apply (rule ext)
  apply (simp add: cte_at_cases obj_at_def)
  apply (rule arg_cong2[where f="op \<or>"])
   apply (safe, simp_all add: a_type_def DomainI)
    apply (clarsimp simp add: a_type_def well_formed_cnode_n_def length_set_helper)
    apply (drule_tac m="fun" in domI)
    apply simp
   apply (case_tac ko, simp_all split: if_split_asm)
   apply (simp add: well_formed_cnode_n_def length_set_helper split: if_split_asm)
  apply (case_tac ko, simp_all split: if_split_asm)
  done

lemma valid_cte_at_typ:
  assumes P: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>cte_at c\<rbrace> f \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  unfolding cte_at_typ
  apply (rule hoare_vcg_disj_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF P])
  apply (rule hoare_vcg_prop)
  done

lemma length_helper:
  "\<exists>y. length y = n"
  apply (rule_tac x="replicate n x" in exI)
  apply simp
  done

lemma pspace_typ_at:
  "kheap s p = Some obj \<Longrightarrow> \<exists>T. typ_at T p s"
  by (clarsimp simp: obj_at_def)


lemma obj_bits_T:
  "obj_bits v = obj_bits_type (a_type v)"
  apply (cases v, simp_all add: obj_bits_type_def a_type_def)
  apply (rule aobj_bits_T)
  done


lemma obj_range_T:
  "obj_range p v = typ_range p (a_type v)"
  by (simp add: obj_range_def typ_range_def obj_bits_T)

lemma valid_untyped_T:
  "valid_untyped c =
  (\<lambda>s. \<forall>T p. \<not>typ_at T p s \<or> typ_range p T \<inter> untyped_range c = {} \<or>
         (typ_range p T \<subseteq> untyped_range c \<and> typ_range p T \<inter> usable_untyped_range c = {}))"
  apply (simp add: valid_untyped_def obj_range_T obj_at_def)
  apply (rule ext)
  apply (rule iffI)
    apply clarsimp
    apply (elim allE)
    apply (erule(1) impE)+
      apply fastforce
  apply clarsimp
    apply (elim allE disjE)
    apply (erule(1) impE)
    apply fastforce+
  done

lemma valid_untyped_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>valid_untyped (UntypedCap dev r n fr)\<rbrace> f
         \<lbrace>\<lambda>rv. valid_untyped (UntypedCap dev r n fr)\<rbrace>"
  unfolding valid_untyped_T
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift [OF P])
  apply (rule hoare_vcg_prop)
  done

lemma cap_aligned_Null [simp]:
  "cap_aligned (NullCap)"
  by (simp add: cap_aligned_def word_bits_def is_aligned_def)


lemma valid_cap_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cap c s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap c s\<rbrace>"
  apply (simp add: valid_cap_def)
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: valid_def)
  apply (case_tac c,
         simp_all add: valid_cap_def P P[where P=id, simplified]
                       ep_at_typ tcb_at_typ ntfn_at_typ sc_obj_at_typ
                       reply_at_typ cap_table_at_typ hoare_vcg_prop)
      apply (rule hoare_vcg_conj_lift [OF valid_untyped_typ[OF P]])
      apply (simp add: valid_def)
     apply (rule hoare_vcg_conj_lift [OF P hoare_vcg_prop])+
   apply (rename_tac option nat)
   apply (case_tac option, simp_all add: tcb_at_typ cap_table_at_typ)[1]
    apply (rule hoare_vcg_conj_lift [OF P])
    apply (rule hoare_vcg_prop)
   apply (rule hoare_vcg_conj_lift [OF P])
   apply (rule hoare_vcg_prop)
  apply (wp valid_arch_cap_typ P)
  done

lemma ntfn_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>ntfn_at c\<rbrace> f \<lbrace>\<lambda>rv. ntfn_at c\<rbrace>"
  by (simp add: ntfn_at_typ)

lemma sc_obj_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>sc_obj_at n c\<rbrace> f \<lbrace>\<lambda>rv. sc_obj_at n c\<rbrace>"
  by (simp add: sc_obj_at_typ)

lemma sc_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>sc_at c\<rbrace> f \<lbrace>\<lambda>rv. sc_at c\<rbrace>"
 by (simp add: sc_at_typ hoare_ex_wp)

lemma reply_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>reply_at c\<rbrace> f \<lbrace>\<lambda>rv. reply_at c\<rbrace>"
  by (simp add: reply_at_typ)

lemma valid_tcb_state_typ:
  assumes P: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_tcb_state st s\<rbrace> f \<lbrace>\<lambda>rv s. valid_tcb_state st s\<rbrace>"
  apply (case_tac st; wpsimp simp: valid_tcb_state_def hoare_post_taut reply_at_typ
                                   ep_at_typ P tcb_at_typ ntfn_at_typ)
   apply (rule hoare_vcg_conj_lift)
    apply (rename_tac obj_ref; case_tac obj_ref;
           simp add: reply_at_typ_at assms wp_post_taut)+
  done

lemma valid_tcb_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_tcb p tcb s\<rbrace> f \<lbrace>\<lambda>rv s. valid_tcb p tcb s\<rbrace>"
  apply (simp add: valid_tcb_def valid_bound_obj_def split_def)
  apply (wp valid_tcb_state_typ valid_cap_typ P hoare_vcg_const_Ball_lift
            valid_case_option_post_wp ntfn_at_typ_at sc_at_typ_at reply_at_typ_at
            valid_arch_tcb_lift)
  done

lemma valid_cs_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cs sz cs s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cs sz cs s\<rbrace>"
  apply (simp add: valid_cs_def)
  apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
  apply (rule hoare_vcg_const_Ball_lift)
  apply (rule valid_cap_typ [OF P])
  done

lemma valid_ep_typ:
  assumes P: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_ep ep s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ep ep s\<rbrace>"
  apply (case_tac ep,
         simp_all add: valid_ep_def hoare_post_taut tcb_at_typ)
   apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
   apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
   apply (rule hoare_vcg_const_Ball_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
  apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
  apply (rule hoare_vcg_const_Ball_lift [OF P])
  done

lemma valid_ntfn_typ:
  assumes P: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  assumes Q: "\<And>p n. \<lbrace>typ_at (ASchedContext n) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (ASchedContext n) p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_ntfn ntfn s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ntfn ntfn s\<rbrace>"
  apply (case_tac "ntfn_obj ntfn",
         simp_all add: valid_ntfn_def valid_bound_obj_def hoare_post_taut tcb_at_typ sc_at_typ)
    defer 2
  apply ((rule hoare_vcg_conj_lift,
         (case_tac "ntfn_bound_tcb ntfn", simp_all add: hoare_post_taut tcb_at_typ P);
         (case_tac "ntfn_sc ntfn", simp_all add: hoare_post_taut hoare_ex_wp sc_at_typ Q))+)[2]
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])+
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_vcg_const_Ball_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
  apply ((case_tac "ntfn_bound_tcb ntfn", simp_all add: hoare_post_taut tcb_at_typ P);
         (case_tac "ntfn_sc ntfn", simp_all add: hoare_post_taut sc_at_typ hoare_ex_wp Q))
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop], simp add: P Q)
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
  apply (rule hoare_vcg_conj_lift; simp add: P hoare_ex_wp Q)
  done

lemma valid_sc_typ_list_all_reply:
  assumes r: "\<And>p. \<lbrace>typ_at AReply p\<rbrace> f \<lbrace>\<lambda>rv. typ_at AReply p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. list_all (\<lambda>r. reply_at r s) xs\<rbrace> f
              \<lbrace>\<lambda>rv s. list_all (\<lambda>r. reply_at r s) xs\<rbrace>"
  by (induct xs)
     (auto simp: wp_post_taut hoare_vcg_conj_lift r[simplified reply_at_typ[symmetric]])

lemma valid_sc_typ:
  (* typ_at or tcb_at, latter is more common due to being an obj_at *)
  assumes t: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  assumes n: "\<And>p. \<lbrace>typ_at ANTFN p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ANTFN p\<rbrace>"
  assumes r: "\<And>p. \<lbrace>typ_at AReply p\<rbrace> f \<lbrace>\<lambda>rv. typ_at AReply p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_sched_context sc s\<rbrace> f \<lbrace>\<lambda>rv s. valid_sched_context sc s\<rbrace>"
  apply (simp add: valid_sched_context_def)
  apply (rule hoare_vcg_conj_lift)
   apply (case_tac "sc_ntfn sc";
          simp add: wp_post_taut n[simplified ntfn_at_typ[symmetric]])
  apply (rule hoare_vcg_conj_lift)
   apply (case_tac "sc_tcb sc";
          simp add: wp_post_taut t[simplified tcb_at_typ[symmetric]])
  apply (rule hoare_vcg_conj_lift)
  apply (case_tac "sc_yield_from sc";
         simp add: wp_post_taut t[simplified tcb_at_typ[symmetric]])
  apply (rule hoare_vcg_conj_lift)
   apply (auto simp: valid_sc_typ_list_all_reply r, wpsimp)
  done

lemma valid_reply_typ:
  assumes t: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  assumes s: "\<And>p n. \<lbrace>typ_at (ASchedContext n) p\<rbrace> f \<lbrace>\<lambda>rv. typ_at (ASchedContext n) p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_reply reply s\<rbrace> f \<lbrace>\<lambda>rv s. valid_reply reply s\<rbrace>"
  apply (simp add: valid_reply_def)
  apply (rule hoare_vcg_conj_lift)
   apply (case_tac "reply_tcb reply";
          simp add: wp_post_taut t[simplified tcb_at_typ[symmetric]])
  apply (case_tac "reply_sc reply";
         simp add: wp_post_taut hoare_ex_wp[OF s] sc_at_typ)
  done

lemma valid_obj_typ:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_obj p ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_obj p ob s\<rbrace>"
  apply (case_tac ob, simp_all add: valid_obj_def P P [where P=id, simplified]
         wellformed_arch_typ valid_sc_typ valid_reply_typ hoare_vcg_prop
         valid_cs_typ valid_tcb_typ valid_ep_typ valid_ntfn_typ hoare_vcg_conj_lift)
  done

lemma valid_irq_node_typ:
  assumes P: "\<And>p. \<lbrace>\<lambda>s. typ_at (ACapTable 0) p s\<rbrace> f \<lbrace>\<lambda>rv s. typ_at (ACapTable 0) p s\<rbrace>"
  assumes Q: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  shows      "\<lbrace>valid_irq_node\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  apply (simp add: valid_irq_node_def cap_table_at_typ)
  apply (wp Q hoare_use_eq [OF Q P] hoare_vcg_all_lift)
  done

lemma wf_cs_upd:
  "\<lbrakk> cs x = Some y \<rbrakk> \<Longrightarrow>
     well_formed_cnode_n n (cs (x \<mapsto> z)) = well_formed_cnode_n n cs"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (subst insert_absorb)
   apply (erule domI)
  apply (rule refl)
  done


lemma cte_wp_at_valid_objs_valid_cap:
  "\<lbrakk> cte_wp_at P p s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>cap. P cap \<and> valid_cap cap s"
  apply (clarsimp simp: cte_wp_at_cases valid_objs_def)
  apply (erule disjE)
   apply clarsimp
   apply (drule bspec, erule domI)
   apply (clarsimp simp: valid_obj_def valid_cs_def)
   apply (drule bspec, erule ranI)
   apply fastforce
  apply clarsimp
  apply (drule bspec, erule domI)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (fastforce simp: ran_def)
  done

lemma is_cap_simps:
  "is_cnode_cap cap = (\<exists>r bits g. cap = CNodeCap r bits g)"
  "is_thread_cap cap = (\<exists>r. cap = ThreadCap r)"
  "is_domain_cap cap = (cap = DomainCap)"
  "is_untyped_cap cap = (\<exists>dev r bits f. cap = UntypedCap dev r bits f)"
  "is_ep_cap cap = (\<exists>r b R. cap = EndpointCap r b R)"
  "is_ntfn_cap cap = (\<exists>r b R. cap = NotificationCap r b R)"
  "is_sched_context_cap cap = (\<exists>r n. cap = SchedContextCap r n)"
  "is_zombie cap = (\<exists>r b n. cap = Zombie r b n)"
  "is_arch_cap cap = (\<exists>a. cap = ArchObjectCap a)"
  "is_reply_cap cap = (\<exists>x. cap = ReplyCap x)"
  by (cases cap, auto simp: is_zombie_def is_arch_cap_def
                            is_reply_cap_def)+


lemma wf_unique:
  "well_formed_cnode_n bits f \<Longrightarrow>
  (THE n. well_formed_cnode_n n f) = bits"
  by (clarsimp simp: well_formed_cnode_n_def length_set_helper)

lemma wf_obj_bits:
  "well_formed_cnode_n bits f \<Longrightarrow> obj_bits (CNode bits f) = cte_level_bits + bits"
  by simp

lemma wf_cs_n_unique:
  "\<lbrakk> well_formed_cnode_n n f; well_formed_cnode_n n' f \<rbrakk>
  \<Longrightarrow> n = n'"
  by (clarsimp simp: well_formed_cnode_n_def length_set_helper)


lemma typ_at_range:
  "\<lbrakk> typ_at T p s; pspace_aligned s; valid_objs s \<rbrakk> \<Longrightarrow> typ_range p T \<noteq> {}"
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: pspace_aligned_def)
  apply (drule bspec)
   apply blast
  apply clarsimp
  apply (case_tac ko)
       apply (clarsimp simp: a_type_def split: if_split_asm)
        apply (clarsimp simp: typ_range_def obj_bits_type_def)
        apply (erule notE)
        apply (erule is_aligned_no_overflow)
       apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def)
      apply (auto simp: a_type_def typ_range_def  obj_bits_type_def
                        aobj_bits_T
                  dest!: is_aligned_no_overflow
                  split: if_split_asm
               | simp)+
  done

lemma typ_at_eq_kheap_obj:
  "typ_at ATCB p s \<longleftrightarrow> (\<exists>tcb. kheap s p = Some (TCB tcb))"
  "typ_at AEndpoint p s \<longleftrightarrow> (\<exists>ep. kheap s p = Some (Endpoint ep))"
  "typ_at ANTFN p s \<longleftrightarrow> (\<exists>ntfn. kheap s p = Some (Notification ntfn))"
  "typ_at (ASchedContext n) p s \<longleftrightarrow>
   (\<exists>sc. kheap s p = Some (SchedContext sc n) \<and> valid_sched_context_size n)"
  "typ_at AReply p s \<longleftrightarrow> (\<exists>reply. kheap s p = Some (Reply reply))"
  "typ_at (ACapTable n) p s \<longleftrightarrow>
   (\<exists>cs. kheap s p = Some (CNode n cs) \<and> well_formed_cnode_n n cs)"
  "typ_at (AGarbage n) p s \<longleftrightarrow>
   (\<exists>cs. n \<ge> cte_level_bits \<and> kheap s p = Some (CNode (n - cte_level_bits) cs) \<and> \<not> well_formed_cnode_n (n - cte_level_bits) cs)
   \<or> (\<exists>sc. \<not> valid_sched_context_size n \<and> kheap s p = Some (SchedContext sc n))"
  apply ((clarsimp simp add: obj_at_def a_type_def; rule iffI; clarsimp),
      case_tac ko; fastforce simp: wf_unique
                             split: if_split_asm kernel_object.splits)+
  apply (clarsimp simp add: obj_at_def a_type_def; rule iffI)
   apply (erule exE)
   apply (case_tac ko; fastforce simp: wf_unique
                                split: if_split_asm kernel_object.splits)
  apply (erule disjE; clarsimp)
  done

lemma a_type_ACapTableE:
  "\<lbrakk>a_type ko = ACapTable n;
    (!!cs. \<lbrakk>ko = CNode n cs; well_formed_cnode_n n cs\<rbrakk> \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemma a_type_AGarbageE:
  "\<lbrakk>a_type ko = AGarbage n;
    (!!cs. \<lbrakk>n \<ge> cte_level_bits; ko = CNode (n - cte_level_bits) cs; \<not>well_formed_cnode_n (n - cte_level_bits) cs\<rbrakk> \<Longrightarrow> R);
    (!!sc. \<lbrakk>\<not>valid_sched_context_size n; ko = SchedContext sc n\<rbrakk> \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm; fastforce)

lemma a_type_ATCBE:
  "\<lbrakk>a_type ko = ATCB; (!!tcb. ko = TCB tcb \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemma a_type_AEndpointE:
  "\<lbrakk>a_type ko = AEndpoint; (!!ep. ko = Endpoint ep \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemma a_type_ANTFNE:
  "\<lbrakk>a_type ko = ANTFN; (!!ntfn. ko = Notification ntfn \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemma a_type_ASchedContextE:
  "\<lbrakk>a_type ko = ASchedContext n; (!!sc. ko = SchedContext sc n \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemma a_type_AReplyE:
  "\<lbrakk>a_type ko = AReply; (!!reply. ko = Reply reply \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: if_split_asm)

lemmas a_type_elims[elim!] =
   a_type_ACapTableE a_type_AGarbageE a_type_ATCBE
   a_type_AEndpointE a_type_ANTFNE a_type_ASchedContextE a_type_AReplyE

lemma valid_objs_caps_contained:
  "\<lbrakk> valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow> caps_contained s"
  unfolding caps_contained_def
  apply (intro allI impI)
  apply (drule (1) cte_wp_at_valid_objs_valid_cap)
  apply (drule (1) cte_wp_at_valid_objs_valid_cap)
  apply clarsimp
  apply (case_tac c, simp_all)
  apply (erule disjE)
   apply (clarsimp simp: valid_cap_def is_cap_simps)
   apply (clarsimp simp: valid_untyped_T)
   apply (simp add: cap_table_at_typ)
   apply (erule allE, erule allE, erule (1) impE)
   apply (drule (2) typ_at_range)
   apply (clarsimp simp: typ_range_def obj_bits_type_def)
   apply fastforce
  apply (clarsimp simp: valid_cap_def is_cap_simps)
  apply (clarsimp simp: valid_untyped_T)
  apply (simp add: tcb_at_typ)
  apply (erule allE, erule allE, erule (1) impE)
  apply (drule (2) typ_at_range)
  apply (clarsimp simp: typ_range_def obj_bits_type_def)
  apply fastforce
  done

lemma P_null_filter_caps_of_cte_wp_at:
  "\<not> P NullCap \<Longrightarrow>
   (null_filter (caps_of_state s) x \<noteq> None \<and> P (the (null_filter (caps_of_state s) x)))
     = (cte_wp_at P x s)"
  by (simp add: cte_wp_at_caps_of_state null_filter_def, fastforce)

lemma cte_wp_at_cte_at:
  "cte_wp_at P p s \<Longrightarrow> cte_at p s"
  by (erule cte_wp_at_weakenE, rule TrueI)

lemma real_cte_at_cte:
  "real_cte_at cref s \<Longrightarrow> cte_at cref s"
  by (cases cref, clarsimp simp: cap_table_at_cte_at)

lemma real_cte_tcb_valid:
  "real_cte_at ptr s \<longrightarrow> tcb_cap_valid cap ptr s"
  by (clarsimp simp: tcb_cap_valid_def obj_at_def is_cap_table is_tcb)

lemma swp_cte_at_caps_of:
  "swp (cte_wp_at P) s = (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> P c)"
  apply (rule ext)
  apply (simp add: cte_wp_at_caps_of_state swp_def)
  done

lemma valid_mdb_def2:
  "valid_mdb = (\<lambda>s. mdb_cte_at (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> NullCap \<noteq> c) (cdt s) \<and>
                    untyped_mdb (cdt s) (caps_of_state s) \<and> descendants_inc (cdt s) (caps_of_state s) \<and>
                    no_mloop (cdt s) \<and> untyped_inc (cdt s) (caps_of_state s) \<and>
                    ut_revocable (is_original_cap s) (caps_of_state s) \<and>
                    irq_revocable (is_original_cap s) (caps_of_state s))"
  by (auto simp add: valid_mdb_def swp_cte_at_caps_of)

lemma cte_wp_valid_cap:
  "\<lbrakk> cte_wp_at (op = c) p s; valid_objs s \<rbrakk> \<Longrightarrow> s \<turnstile> c"
  apply (simp add: cte_wp_at_cases)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: valid_objs_def dom_def)
   apply (erule allE, erule impE, fastforce)
   apply (fastforce simp: ran_def valid_obj_def valid_cs_def)
  apply clarsimp
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, fastforce)
  apply (fastforce simp: ran_def valid_obj_def valid_tcb_def)
  done

lemma cte_wp_tcb_cap_valid:
  "\<lbrakk> cte_wp_at (op = c) p s; valid_objs s \<rbrakk> \<Longrightarrow> tcb_cap_valid c p s"
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def cte_wp_at_cases)
  apply (erule disjE, (clarsimp simp: is_tcb)+)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule bspec, erule ranI, simp)
  apply clarsimp
  done

lemma caps_of_state_cte_at:
  "caps_of_state s p = Some c \<Longrightarrow> cte_at p s"
  by (simp add: cte_wp_at_caps_of_state)

lemma cte_wp_cte_at:
  "cte_wp_at P p s \<Longrightarrow> cte_at p s"
  by (auto simp add: cte_wp_at_cases)


context pspace_update_eq begin

interpretation Arch_pspace_update_eq ..

lemma valid_space_update [iff]:
  "valid_pspace (f s) = valid_pspace s"
  by (fastforce intro: valid_pspace_eqI simp: pspace)

lemmas obj_at_update [iff] = obj_at_update
lemmas arch_valid_obj_update [iff] = arch_valid_obj_update

lemma cte_wp_at_update [iff]:
  "cte_wp_at P p (f s) = cte_wp_at P p s"
  by (fastforce intro: cte_wp_at_pspaceI simp: pspace)

lemma iflive_update [iff]:
  "if_live_then_nonz_cap (f s) = if_live_then_nonz_cap s"
  by (simp add: if_live_then_nonz_cap_def ex_nonz_cap_to_def)

lemma valid_objs_update [iff]:
  "valid_objs (f s) = valid_objs s"
  by (fastforce intro: valid_objs_pspaceI simp: pspace)

lemma pspace_aligned_update [iff]:
  "pspace_aligned (f s) = pspace_aligned s"
  by (simp add: pspace_aligned_def pspace)

lemma pspace_distinct_update [iff]:
  "pspace_distinct (f s) = pspace_distinct s"
  by (simp add: pspace_distinct_def pspace)

lemma pred_tcb_at_update [iff]:
  "pred_tcb_at proj P p (f s) = pred_tcb_at proj P p s"
  by (simp add: pred_tcb_at_def)

lemma valid_cap_update [iff]:
  "(f s) \<turnstile> c = s \<turnstile> c"
  by (auto intro: valid_cap_pspaceI simp: pspace)

lemmas get_cap_update [iff] = get_cap_update
lemmas caps_of_state_update [iff] = caps_of_state_update

lemma valid_refs_update [iff]:
  "valid_refs R (f s) = valid_refs R s"
  by (simp add: valid_refs_def)

lemma has_reply_cap_update [iff]:
  "has_reply_cap t (f s) = has_reply_cap t s"
  by (simp add: has_reply_cap_def)

lemmas in_user_frame_update[iff] = in_user_frame_update
lemmas in_device_frame_update[iff] = in_device_frame_update
lemmas equal_kernel_mappings_update[iff] = equal_kernel_mappings_update

end


context p_arch_update_eq begin

interpretation Arch_p_arch_update_eq f ..

lemma valid_vspace_objs_update [iff]:
  "valid_vspace_objs (f s) = valid_vspace_objs s"
  by (simp add: valid_vspace_objs_def)

lemma valid_arch_cap_update [iff]:
  "valid_arch_caps (f s) = valid_arch_caps s"
  by (simp add: valid_arch_caps_def)

lemma valid_global_objs_update [iff]:
  "valid_global_objs (f s) = valid_global_objs s"
  by (simp add: valid_global_objs_def arch)

lemma valid_global_vspace_mappings_update [iff]:
  "valid_global_vspace_mappings (f s) = valid_global_vspace_mappings s"
  by (simp add: valid_global_vspace_mappings_def arch)

lemma pspace_in_kernel_window_update [iff]:
  "pspace_in_kernel_window (f s) = pspace_in_kernel_window s"
  by (simp add: pspace_in_kernel_window_def arch pspace)

lemma cap_refs_in_kernel_window_update [iff]:
  "cap_refs_in_kernel_window (f s) = cap_refs_in_kernel_window s"
  by (simp add: cap_refs_in_kernel_window_def arch pspace)

end


context p_arch_idle_update_eq begin

interpretation Arch_p_arch_idle_update_eq f ..

lemma ifunsafe_update [iff]:
  "if_unsafe_then_cap (f s) = if_unsafe_then_cap s"
  by (simp add: if_unsafe_then_cap_def ex_cte_cap_wp_to_def irq)

lemma valid_global_refs_update [iff]:
  "valid_global_refs (f s) = valid_global_refs s"
  by (simp add: valid_global_refs_def arch idle)

lemma valid_asid_map_update [iff]:
  "valid_asid_map (f s) = valid_asid_map s"
  by (simp add: valid_asid_map_def vspace_at_asid_def arch)

lemma valid_arch_state_update [iff]:
  "valid_arch_state (f s) = valid_arch_state s"
  by (simp add: valid_arch_state_def arch split: option.split)

lemma valid_idle_update [iff]:
  "valid_idle (f s) = valid_idle s"
  by (auto intro: valid_idle_pspaceI simp: pspace idle)

lemma valid_kernel_mappings_update [iff]:
  "valid_kernel_mappings (f s) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def
                pspace arch)

lemma only_idle_update [iff]:
  "only_idle (f s) = only_idle s"
  by (simp add: only_idle_def idle)

lemma valid_irq_node_update[iff]:
  "valid_irq_node (f s) = valid_irq_node s"
  by (simp add: valid_irq_node_def irq)

end

lemma (in irq_states_update_eq) irq_issued_update [iff]:
  "irq_issued irq (f s) = irq_issued irq s"
  by (simp add: irq_issued_def int)

lemma (in pspace_int_update_eq) valid_irq_handlers_update [iff]:
  "valid_irq_handlers (f s) = valid_irq_handlers s"
  by (simp add: valid_irq_handlers_def)

context arch_idle_update_eq begin
interpretation Arch_arch_idle_update_eq f ..
lemmas global_refs_update[iff] = global_refs_update
end

interpretation revokable_update:
  p_arch_idle_update_int_eq "is_original_cap_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> revokable_update: Arch_p_arch_idle_update_int_eq "is_original_cap_update f" ..

interpretation machine_state_update:
  p_arch_idle_update_int_eq "machine_state_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> machine_state_update: Arch_p_arch_idle_update_int_eq "machine_state_update f" ..

interpretation cdt_update:
  p_arch_idle_update_int_eq "cdt_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> cdt_update: Arch_p_arch_idle_update_int_eq "cdt_update f" ..

interpretation cur_thread_update:
  p_arch_idle_update_int_eq "cur_thread_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> cur_thread_update: Arch_p_arch_idle_update_int_eq "cur_thread_update f" ..

interpretation more_update:
  p_arch_idle_update_int_eq "trans_state f"
  by unfold_locales auto

sublocale Arch \<subseteq> more_update: Arch_p_arch_idle_update_int_eq "trans_state f" ..

interpretation interrupt_update:
  p_arch_idle_update_eq "interrupt_states_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> interrupt_update: Arch_p_arch_idle_update_eq "interrupt_states_update f" ..

interpretation consumed_time_update_arch:
  p_arch_idle_update_int_eq "consumed_time_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> consumed_time_update_arch: Arch_p_arch_idle_update_int_eq "consumed_time_update f" ..

interpretation cur_time_update_arch:
  p_arch_idle_update_int_eq "cur_time_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> cur_time_update_arch: Arch_p_arch_idle_update_int_eq "cur_time_update f" ..

interpretation cur_sc_update_arch:
  p_arch_idle_update_int_eq "cur_sc_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> cur_sc_update_arch: Arch_p_arch_idle_update_int_eq "cur_sc_update f" ..

interpretation reprogram_timer_update_arch:
  p_arch_idle_update_int_eq "reprogram_timer_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> reprogram_timer_update_arch: Arch_p_arch_idle_update_int_eq "reprogram_timer_update f" ..

interpretation irq_node_update:
  pspace_int_update_eq "interrupt_irq_node_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> irq_node_update: Arch_pspace_update_eq "interrupt_irq_node_update f" ..

interpretation arch_update:
  pspace_int_update_eq "arch_state_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> arch_update: Arch_pspace_update_eq "arch_state_update f" ..

interpretation irq_node_update_arch:
  p_arch_update_eq "interrupt_irq_node_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> irq_node_update_arch: Arch_p_arch_update_eq "interrupt_irq_node_update f" ..

lemma obj_ref_in_untyped_range:
  "\<lbrakk> is_untyped_cap c; cap_aligned c \<rbrakk> \<Longrightarrow> obj_ref_of c \<in> untyped_range c"
  apply (clarsimp simp: is_cap_simps cap_aligned_def)
  apply (erule is_aligned_no_overflow)
  done

lemma untyped_range_non_empty:
  "\<lbrakk> is_untyped_cap c; cap_aligned c \<rbrakk> \<Longrightarrow> untyped_range c \<noteq> {}"
  by (blast dest: obj_ref_in_untyped_range)

lemma valid_mdb_cur [iff]:
  "valid_mdb (cur_thread_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_more_update [iff]:
  "valid_mdb (trans_state f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_machine [iff]:
  "valid_mdb (machine_state_update f s) = valid_mdb s"
  by (auto elim: valid_mdb_eqI)

lemma valid_mdb_consumed_time_update [iff]:
  "valid_mdb (consumed_time_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_cur_time_update [iff]:
  "valid_mdb (cur_time_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_cur_sc_update [iff]:
  "valid_mdb (cur_sc_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_reprogram_timer_update [iff]:
  "valid_mdb (reprogram_timer_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_refs_cte:
  assumes "\<And>P p. cte_wp_at P p s = cte_wp_at P p s'"
  shows "valid_refs R s = valid_refs R s'"
  by (simp add: valid_refs_def assms)

lemma valid_refs_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_refs R s\<rbrace> f \<lbrace>\<lambda>_ s. valid_refs R s\<rbrace>"
  apply (simp add: valid_refs_def2)
  apply (rule ctes)
  done


lemma valid_global_refs_cte:
  assumes "\<And>P p. cte_wp_at P p s = cte_wp_at P p s'"
  assumes "global_refs s = global_refs s'"
  shows "valid_global_refs s = valid_global_refs s'"
  apply (simp add: valid_global_refs_def)
  by (simp add: valid_global_refs_def assms valid_refs_def)


lemma valid_global_refs_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  assumes irq: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  shows "\<lbrace>valid_global_refs\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  unfolding valid_global_refs_def valid_refs_def2
  apply (rule hoare_lift_Pf [where f="caps_of_state", OF _ ctes])
  apply (rule global_refs_lift[OF arch idle irq])
  done


lemma has_reply_cap_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> f \<lbrace>\<lambda>_ s. P (has_reply_cap t s)\<rbrace>"
  unfolding has_reply_cap_def
  by (simp add: cte_wp_at_caps_of_state, rule ctes)

lemma pred_tcb_at_disj:
  "(pred_tcb_at proj P t s \<or> pred_tcb_at proj Q t s) = pred_tcb_at proj (\<lambda>a. P a \<or> Q a) t s"
  by (fastforce simp add: pred_tcb_at_def obj_at_def)

lemma dom_empty_cnode: "dom (empty_cnode us) = {x. length x = us}"
  unfolding empty_cnode_def
  by (simp add: dom_def)

lemma obj_at_default_cap_valid:
  "\<lbrakk>obj_at (\<lambda>ko. ko = default_object ty dev us) x s;
   ty = CapTableObject \<Longrightarrow> 0 < us;
   ty = SchedContextObject \<Longrightarrow> valid_sched_context_size us;
   ty \<noteq> Untyped; ty \<noteq> ArchObject ASIDPoolObj;
   cap_aligned (default_cap ty x us dev)\<rbrakk>
  \<Longrightarrow> s \<turnstile> default_cap ty x us dev"
  unfolding valid_cap_def
  by (clarsimp elim!: obj_at_weakenE
      intro!: aobj_at_default_arch_cap_valid
      simp: default_object_def dom_empty_cnode well_formed_cnode_n_def
            is_tcb is_ep is_ntfn is_reply is_cap_table
            a_type_def obj_at_def is_sc_obj_def
     split: apiobject_type.splits
            option.splits)


lemma obj_ref_default [simp]:
  "obj_ref_of (default_cap ty x us dev) = x"
  by (cases ty, auto simp: aobj_ref_default)

lemma valid_pspace_aligned2 [elim!]:
  "valid_pspace s \<Longrightarrow> pspace_aligned s"
  by (simp add: valid_pspace_def)

lemma valid_pspace_distinct [elim!]:
  "valid_pspace s \<Longrightarrow> pspace_distinct s"
  by (simp add: valid_pspace_def)

lemma ctable_vtable_neq [simp]:
  "get_tcb_ctable_ptr ptr \<noteq> get_tcb_vtable_ptr ptr"
  unfolding get_tcb_ctable_ptr_def get_tcb_vtable_ptr_def
  by simp

lemma ep_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>ep_at c\<rbrace> f \<lbrace>\<lambda>rv. ep_at c\<rbrace>"
  by (simp add: ep_at_typ)

lemma tcb_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>tcb_at c\<rbrace> f \<lbrace>\<lambda>rv. tcb_at c\<rbrace>"
  by (simp add: tcb_at_typ)

lemma cap_table_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>cap_table_at n c\<rbrace> f \<lbrace>\<lambda>rv. cap_table_at n c\<rbrace>"
  by (simp add: cap_table_at_typ)


lemmas abs_typ_at_lifts  =
  ep_at_typ_at ntfn_at_typ_at tcb_at_typ_at
  cap_table_at_typ_at sc_at_typ_at reply_at_typ_at
  valid_tcb_state_typ valid_cte_at_typ valid_ntfn_typ valid_sc_typ
  valid_ep_typ valid_cs_typ valid_untyped_typ valid_reply_typ
  valid_tcb_typ valid_obj_typ valid_cap_typ valid_vspace_obj_typ

lemma valid_idle_lift:
  assumes "\<And>P t. \<lbrace>idle_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. idle_tcb_at P t\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>valid_idle\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: valid_idle_def)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule hoare_vcg_conj_lift)
    apply (rule assms)+
  done


lemmas caps_of_state_valid_cap = cte_wp_valid_cap [OF caps_of_state_cteD]


lemma (in Arch) obj_ref_is_arch:
  "\<lbrakk>aobj_ref c = Some r; valid_arch_cap c s\<rbrakk> \<Longrightarrow> \<exists> ako. kheap s r = Some (ArchObj ako)"
by (auto simp add: valid_arch_cap_def obj_at_def split: arch_cap.splits if_splits)


requalify_facts Arch.obj_ref_is_arch


lemma obj_ref_is_tcb:
  "\<lbrakk> r \<in> obj_refs cap; tcb_at r s; s \<turnstile> cap \<rbrakk> \<Longrightarrow>
  is_thread_cap cap \<or> is_zombie cap"
  by (auto simp: valid_cap_def is_cap_simps obj_at_def is_obj_defs a_type_def
          split: cap.splits
           dest: obj_ref_is_arch)

lemma obj_ref_is_cap_table:
  "\<lbrakk> r \<in> obj_refs cap; cap_table_at n r s; s \<turnstile> cap \<rbrakk> \<Longrightarrow>
  is_cnode_cap cap \<or> is_zombie cap"
  by (auto simp: valid_cap_def is_cap_simps obj_at_def is_obj_defs a_type_def
           dest: obj_ref_is_arch
           split: cap.splits if_split_asm)

lemma ut_revocableD:
  "\<lbrakk> cs p = Some cap; is_untyped_cap cap; ut_revocable r cs \<rbrakk> \<Longrightarrow> r p"
  by (auto simp: ut_revocable_def)

lemma untyped_range_is_untyped_cap [elim!]:
  "untyped_range cap \<noteq> {} \<Longrightarrow> is_untyped_cap cap"
  by (cases cap) auto

lemma not_is_untyped_no_range [elim!]:
  "\<not>is_untyped_cap cap \<Longrightarrow> untyped_range cap = {}"
  by (cases cap) auto

lemma untyped_mdbD:
  "\<lbrakk> cs ptr = Some cap; is_untyped_cap cap; cs ptr' = Some cap';
     obj_refs cap' \<inter> untyped_range cap \<noteq> {}; untyped_mdb m cs \<rbrakk>
  \<Longrightarrow> ptr' \<in> descendants_of ptr m"
  unfolding untyped_mdb_def by blast

lemma untyped_incD:
  "\<lbrakk> cs p = Some c; is_untyped_cap c; cs p' = Some c'; is_untyped_cap c'; untyped_inc m cs \<rbrakk> \<Longrightarrow>
  (untyped_range c \<subseteq> untyped_range c' \<or> untyped_range c' \<subseteq> untyped_range c \<or> untyped_range c \<inter> untyped_range c' = {}) \<and>
  (untyped_range c \<subset> untyped_range c' \<longrightarrow> (p \<in> descendants_of p' m \<and> untyped_range c \<inter> usable_untyped_range c' = {})) \<and>
  (untyped_range c' \<subset> untyped_range c \<longrightarrow> (p' \<in> descendants_of p m \<and> untyped_range c' \<inter> usable_untyped_range c = {})) \<and>
  (untyped_range c = untyped_range c' \<longrightarrow> (p' \<in> descendants_of p m \<and> usable_untyped_range c = {}
  \<or> p \<in> descendants_of p' m \<and> usable_untyped_range c' = {} \<or> p = p'))"
  unfolding untyped_inc_def
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (elim allE impE)
    apply simp+
  done

lemma cte_wp_at_norm:
  "cte_wp_at P p s \<Longrightarrow> \<exists>c. cte_wp_at (op = c) p s \<and> P c"
  by (auto simp add: cte_wp_at_cases)

lemma valid_mdb_arch_state [simp]:
  "valid_mdb (arch_state_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_idle_arch_state [simp]:
  "valid_idle (arch_state_update f s) = valid_idle s"
  by (simp add: valid_idle_def)

lemma if_unsafe_then_cap_arch_state [simp]:
  "if_unsafe_then_cap (arch_state_update f s) = if_unsafe_then_cap s"
  by (simp add: if_unsafe_then_cap_def ex_cte_cap_wp_to_def)

lemma swp_cte_at_arch_update [iff]:
  "swp cte_at (s\<lparr>arch_state := a\<rparr>) = swp cte_at s"
  by (simp add: cte_wp_at_cases swp_def)

lemma swp_caps_of_state_arch_update [iff]:
  "caps_of_state (s\<lparr>arch_state := a\<rparr>) = caps_of_state s"
  apply (rule cte_wp_caps_of_lift)
  apply (simp add: cte_wp_at_cases)
  done

(* FIXME: duplicated with caps_of_state_valid_cap *)
lemmas caps_of_state_valid =  caps_of_state_valid_cap

lemma valid_cap_aligned:
  "s \<turnstile> cap \<Longrightarrow> cap_aligned cap"
  by (simp add: valid_cap_def)

lemma valid_pspace_vo [elim!]:
  "valid_pspace s \<Longrightarrow> valid_objs s"
  by (simp add: valid_pspace_def)

lemma pred_tcb_at_conj_strg:
  "pred_tcb_at proj P t s \<and> pred_tcb_at proj Q t s \<longrightarrow> pred_tcb_at proj (\<lambda>a. P a \<and> Q a) t s"
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma real_cte_at_typ_valid:
  "\<lbrace>typ_at (ACapTable (length (snd p))) (fst p)\<rbrace>
     f
   \<lbrace>\<lambda>rv. typ_at (ACapTable (length (snd p))) (fst p)\<rbrace>
   \<Longrightarrow> \<lbrace>real_cte_at p\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at p\<rbrace>"
  by (simp add: cap_table_at_typ)

lemma dmo_aligned:
  "\<lbrace>pspace_aligned\<rbrace> do_machine_op f \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pspace_aligned_def)
  done

lemma cte_wp_at_eqD2:
  "\<lbrakk>cte_wp_at (op = c) p s; cte_wp_at P p s \<rbrakk> \<Longrightarrow> P c"
  by (auto elim!: cte_wp_atE split: if_split_asm)

lemma not_pred_tcb:
  "(\<not>pred_tcb_at proj P t s) = (\<not>tcb_at t s \<or> pred_tcb_at proj (\<lambda>a. \<not>P a) t s)"
  apply (simp add: pred_tcb_at_def obj_at_def is_tcb_def)
  apply (auto split: kernel_object.splits)
  done


lemma only_idle_arch [iff]:
  "only_idle (arch_state_update f s) = only_idle s"
  by (simp add: only_idle_def)

(* TODO: move to Wellform before the instantiation. should be instantiated retroactively, but isn't. *)
(* FIXME: would be nice to be in the iff-set. *)
lemma (in pspace_update_eq) state_refs_update:
  "state_refs_of (f s) = state_refs_of s"
  by (simp add: state_refs_of_def pspace cong: option.case_cong)

lemmas (in pspace_update_eq) state_hyp_refs_update[iff] = state_hyp_refs_update[OF  pspace]

declare more_update.state_refs_update[iff]
declare more_update.state_hyp_refs_update[iff]

lemma zombies_final_arch_update [iff]:
  "zombies_final (arch_state_update f s) = zombies_final s"
  by (simp add: zombies_final_def is_final_cap'_def)

lemma zombies_final_more_update [iff]:
  "zombies_final (trans_state f s) = zombies_final s"
  by (simp add: zombies_final_def is_final_cap'_def)

lemma zombies_final_consumed_time_update[simp]:
  "zombies_final (consumed_time_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)

lemma zombies_final_cur_time_update[simp]:
  "zombies_final (cur_time_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)

lemma zombies_final_cur_sc_update[simp]:
  "zombies_final (cur_sc_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)

lemma zombies_final_reprogram_timer_update[simp]:
  "zombies_final (reprogram_timer_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)

lemmas state_refs_arch_update [iff] = arch_update.state_refs_update

lemmas state_hyp_refs_arch_update [iff] = arch_update.state_hyp_refs_update

lemma valid_ioc_arch_state_update[iff]:
  "valid_ioc (arch_state_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma valid_ioc_more_update[iff]:
  "valid_ioc (trans_state f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma valid_ioc_interrupt_states_update[iff]:
  "valid_ioc (interrupt_states_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_machine_state_update[iff]:
  "valid_ioc (machine_state_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_cur_thread_update[iff]:
  "valid_ioc (cur_thread_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma valid_ioc_consumed_time_update[iff]:
  "valid_ioc (consumed_time_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma valid_ioc_cur_time_update[iff]:
  "valid_ioc (cur_time_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_cur_sc_update[iff]:
  "valid_ioc (cur_sc_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_reprogram_timer_update[iff]:
  "valid_ioc (reprogram_timer_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma vms_ioc_update[iff]:
  "valid_machine_state (is_original_cap_update f s::'z::state_ext state) = valid_machine_state s"
  by (simp add: valid_machine_state_def)+

lemma valid_machine_state_more_update[iff]:
  "valid_machine_state (trans_state f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

lemma only_idle_lift_weak:
  assumes "\<And>Q P t. \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace> f \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>only_idle\<rbrace> f \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: only_idle_def)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule assms)+
  done

lemma only_idle_lift:
  assumes T: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes s: "\<And>P t. \<lbrace>st_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>only_idle\<rbrace> f \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: only_idle_def)
  apply (rule hoare_vcg_all_lift)
  apply (subst imp_conv_disj not_pred_tcb)+
  apply (rule hoare_vcg_disj_lift)+
    apply (simp add: tcb_at_typ)
    apply (rule T)
   apply (rule s)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule assms)+
  done


lemma cap_rights_update_id [intro!, simp]:
  "wellformed_cap c \<Longrightarrow> cap_rights_update (cap_rights c) c = c"
  unfolding cap_rights_update_def
  by (cases c) (auto simp: wellformed_cap_simps)

lemma cap_mask_UNIV [simp]:
  "wellformed_cap c \<Longrightarrow> mask_cap UNIV c = c"
by (simp add: mask_cap_def)

lemma wf_empty_bits:
  "well_formed_cnode_n bits (empty_cnode bits)"
  by (simp add: well_formed_cnode_n_def empty_cnode_def dom_def)

lemma well_formed_cnode_valid_cs_size:
  "valid_cs_size bits s \<Longrightarrow> well_formed_cnode_n bits s"
  by (clarsimp simp: valid_cs_size_def)

lemma empty_cnode_bits:
  "obj_bits (CNode n (empty_cnode n)) = cte_level_bits + n"
  by (simp add: wf_empty_bits)

lemma irq_revocableD:
  "\<lbrakk> cs p = Some IRQControlCap; irq_revocable (is_original_cap s) cs \<rbrakk> \<Longrightarrow> is_original_cap s p"
  by (fastforce simp add: irq_revocable_def simp del: split_paired_All)

lemma invs_valid_stateI [elim!]:
  "invs s \<Longrightarrow> valid_state s"
  by (simp add: invs_def)

lemma tcb_at_invs [elim!]:
  "invs s \<Longrightarrow> tcb_at (cur_thread s) s"
  by (simp add: invs_def cur_tcb_def)

lemma valid_irq_states_more_update[iff]:
  "valid_irq_states (trans_state f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)


lemma invs_valid_objs [elim!]:
  "invs s \<Longrightarrow> valid_objs s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_psp_aligned [elim!]:
  "invs s \<Longrightarrow> pspace_aligned s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_mdb [elim!]:
  "invs s \<Longrightarrow> valid_mdb s"
  by (simp add: invs_def valid_state_def)

lemma invs_mdb_cte [elim!]:
  "invs s \<Longrightarrow> mdb_cte_at (swp (cte_wp_at (op \<noteq> NullCap)) s) (cdt s)"
  by (simp add: invs_def valid_state_def valid_mdb_def)

lemma invs_valid_pspace [elim!]:
  "invs s \<Longrightarrow> valid_pspace s"
  by (simp add: invs_def valid_state_def)

lemma invs_arch_state [elim!]:
  "invs s \<Longrightarrow> valid_arch_state s"
  by (simp add: invs_def valid_state_def)

lemma invs_cur [elim!]:
  "invs s \<Longrightarrow> cur_tcb s"
  by (simp add: invs_def)

lemma invs_distinct [elim!]:
  "invs s \<Longrightarrow> pspace_distinct s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_iflive [elim!]:
  "invs s \<Longrightarrow> if_live_then_nonz_cap s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_sym_refs [elim!]:
  "invs s \<Longrightarrow> sym_refs (state_refs_of s)"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_hyp_sym_refs [elim!]: (* ARMHYP move and requalify *)
  "invs s \<Longrightarrow> sym_refs (state_hyp_refs_of s)"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_vobjs_strgs:
  "invs s \<longrightarrow> valid_objs s"
  by auto

lemma invs_valid_global_refs [elim!]:
  "invs s \<Longrightarrow> valid_global_refs s"
  by (simp add: invs_def valid_state_def)

lemma invs_zombies [elim!]:
  "invs s \<Longrightarrow> zombies_final s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma objs_valid_tcb_ctable:
  "\<lbrakk>valid_objs s; get_tcb t s = Some tcb\<rbrakk> \<Longrightarrow> s \<turnstile> tcb_ctable tcb"
  apply (clarsimp simp: get_tcb_def split: option.splits kernel_object.splits)
  apply (erule cte_wp_valid_cap[rotated])
  apply (rule cte_wp_at_tcbI[where t="(a, b)" for a b, where b3="tcb_cnode_index 0"])
    apply fastforce+
  done

lemma invs_valid_tcb_ctable:
  "\<lbrakk>invs s; get_tcb t s = Some tcb\<rbrakk> \<Longrightarrow> s \<turnstile> tcb_ctable tcb"
  apply (drule invs_valid_stateI)
  apply (clarsimp simp: valid_state_def valid_pspace_def objs_valid_tcb_ctable)
  done

lemma invs_vspace_objs [elim!]:
  "invs s \<Longrightarrow> valid_vspace_objs s"
  by (simp add: invs_def valid_state_def)

lemma invs_valid_idle[elim!]:
  "invs s \<Longrightarrow> valid_idle s"
  by (fastforce simp: invs_def valid_state_def)

(* not used anywhere
lemma simple_st_tcb_at_state_refs_ofD:
  "st_tcb_at simple t s \<Longrightarrow> bound_tcb_at (\<lambda>x. get_refs TCBBound x = state_refs_of s t) t s"
  by (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def)
*)
lemma active_st_tcb_at_state_refs_ofD:
  "st_tcb_at active t s \<Longrightarrow> st_tcb_at (\<lambda>x. tcb_st_refs_of x = {}) t s"
  by (auto simp: pred_tcb_at_def obj_at_def split: thread_state.splits)

(* need a new version? or the above lemma should suffice?
lemma active_st_tcb_at_state_refs_ofD:
  "st_tcb_at active t s \<Longrightarrow> bound_tcb_at (\<lambda>x. get_refs TCBBound x = state_refs_of s t) t s"
  by (clarsimp simp: pred_tcb_at_def obj_at_def state_refs_of_def)
*)
lemma cur_tcb_revokable [iff]:
  "cur_tcb (is_original_cap_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma cur_tcb_arch [iff]:
  "cur_tcb (arch_state_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma invs_valid_global_objs[elim!]:
  "invs s \<Longrightarrow> valid_global_objs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma get_irq_slot_real_cte:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>real_cte_at\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def
    valid_irq_node_def)
  done

lemma all_invs_but_sym_refs_check:
  "(all_invs_but_sym_refs and sym_refs \<circ> state_refs_of and sym_refs o state_hyp_refs_of) = invs"
  by (simp add: invs_def valid_state_def valid_pspace_def
                o_def pred_conj_def conj_comms)



lemma invs_valid_asid_map[elim!]:
  "invs s \<Longrightarrow> valid_asid_map s"
  by (simp add: invs_def valid_state_def)

lemma invs_equal_kernel_mappings[elim!]:
  "invs s \<Longrightarrow> equal_kernel_mappings s"
  by (simp add:invs_def valid_state_def)

lemma invs_valid_irq_node[elim!]:
  "invs s \<Longrightarrow> valid_irq_node s"
  by (simp add: invs_def valid_state_def)

lemma invs_ifunsafe[elim!]:
  "invs s \<Longrightarrow> if_unsafe_then_cap s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma cte_wp_at_cap_aligned:
  "\<lbrakk>cte_wp_at P p s; invs s\<rbrakk> \<Longrightarrow> \<exists>c. P c \<and> cap_aligned c"
  apply (drule (1) cte_wp_at_valid_objs_valid_cap [OF _ invs_valid_objs])
  apply (fastforce simp: valid_cap_def)
  done

lemma cte_wp_at_cap_aligned':
  "\<lbrakk>cte_wp_at (op = cap) p s; invs s\<rbrakk> \<Longrightarrow> cap_aligned cap"
  apply (drule (1) cte_wp_at_valid_objs_valid_cap [OF _ invs_valid_objs])
  apply (fastforce simp: valid_cap_def)
  done

locale invs_locale =
  fixes ex_inv :: "'z::state_ext state \<Rightarrow> bool"
  assumes dmo_ex_inv[wp]: "\<And>f. \<lbrace>invs and ex_inv\<rbrace> do_machine_op f \<lbrace>\<lambda>rv::unit. ex_inv\<rbrace>"
  assumes cap_insert_ex_inv[wp]: "\<And>cap src dest.
  \<lbrace>ex_inv and invs and K (src \<noteq> dest)\<rbrace>
      cap_insert cap src dest
  \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes cap_delete_one_ex_inv[wp]: "\<And>cap.
   \<lbrace>ex_inv and invs\<rbrace> cap_delete_one cap \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes set_endpoint_ex_inv[wp]: "\<And>a b.\<lbrace>ex_inv\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes sts_ex_inv[wp]: "\<And>a b. \<lbrace>ex_inv\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes do_ipc_transfer_ex_inv[wp]: "\<And>a b c d e. \<lbrace>ex_inv and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes thread_set_ex_inv[wp]: "\<And>a b. \<lbrace>ex_inv\<rbrace> thread_set a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"

lemma invs_locale_trivial:
  "invs_locale \<top>"
  by (unfold_locales; wp)

lemma in_dxo_pspaceD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> kheap s' = kheap s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_cdtD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> cdt s' = cdt s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_revokableD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> is_original_cap s' = is_original_cap s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_cur_threadD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> cur_thread s' = cur_thread s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_idle_threadD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> idle_thread s' = idle_thread s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_machine_stateD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> machine_state s' = machine_state s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_irq_nodeD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> interrupt_irq_node s' = interrupt_irq_node s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_interruptD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> interrupt_states s' = interrupt_states s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_archD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> arch_state s' = arch_state s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma sym_refs_bound_tcb_atD: (* RT: other versions? *)
  "\<lbrakk>bound_tcb_at P t s; sym_refs (state_refs_of s)\<rbrakk>
    \<Longrightarrow> \<exists>ts ntfnptr scptr1 ytptr.
        P ntfnptr \<and>
        obj_at (tcb_ntfn_is_bound ntfnptr) t s
        \<and> obj_at (tcb_sc_is_bound scptr1) t s
        \<and> state_refs_of s t = tcb_st_refs_of ts \<union> get_refs TCBBound ntfnptr
         \<union> get_refs TCBSchedContext scptr1
         \<union> get_refs TCBYieldTo ytptr
        \<and> (\<forall>(x, tp)\<in>tcb_st_refs_of ts \<union> get_refs TCBBound ntfnptr
         \<union> get_refs TCBSchedContext scptr1
         \<union> get_refs TCBYieldTo ytptr.
            obj_at (\<lambda>ko. (t, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule bound_tcb_at_state_refs_ofD)
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply (rule_tac x=scptr1 in exI)
  apply (rule_tac x=ytptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD)
  apply (drule (1)sym_refs_obj_atD)
  apply auto
  done


lemma vs_lookup_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'"
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_pages_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'"
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce dest: ko elim: vs_lookup_pages1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed

end
