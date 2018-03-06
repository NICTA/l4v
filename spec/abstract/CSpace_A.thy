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
Abstract model of CSpace.
*)

chapter "CSpace"

theory CSpace_A
imports
  SchedContext_A
  IpcCancel_A
  "../../lib/Monad_WP/NonDetMonadLemmas"
  "~~/src/HOL/Library/Prefix_Order"
begin

context begin interpretation Arch .

requalify_consts
  arch_update_cap_data
  arch_derive_cap
  arch_finalise_cap
  arch_is_physical
  arch_same_region_as
  same_aobject_as
  prepare_thread_delete
  
  cap_transfer_data_size
  msg_max_extra_caps
  msg_align_bits
  update_cnode_cap_data
  cnode_padding_bits
  cnode_guard_size_bits

end


text {* This theory develops an abstract model of \emph{capability
spaces}, or CSpace, in seL4. The CSpace of a thread can be thought of
as the set of all capabilities it has access to. More precisely, it
is a directed graph of CNodes starting in the CSpace slot of a TCB.
Capabilities are accessed from the user side by specifying a path in this
graph. The kernel internally uses references to CNodes with an index into
the CNode to identify capabilities.

The following sections show basic manipulation of capabilities,
resolving user-specified, path-based capability references into
internal kernel references, transfer, revokation, deletion,
and finally toplevel capability invocations.
*}

section {* Basic capability manipulation *}

text {* Interpret a set of rights from a user data word. *}
definition
  data_to_rights :: "data \<Rightarrow> cap_rights" where
  "data_to_rights data \<equiv> let
    w = data_to_16 data
   in {x. case x of AllowWrite \<Rightarrow> w !! 0
                  | AllowRead \<Rightarrow> w !! 1
                  | AllowGrant \<Rightarrow> w !! 2}"

text {* Check that a capability stored in a slot is not a parent of any other
capability. *}
definition
  ensure_no_children :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) se_monad" where
  "ensure_no_children cslot_ptr \<equiv> doE
    cdt \<leftarrow> liftE $ gets cdt;
    whenE (\<exists>c. cdt c = Some cslot_ptr) (throwError RevokeFirst)
  odE"

definition
  max_free_index :: "nat \<Rightarrow> nat" where
  "max_free_index magnitude_bits \<equiv> 2 ^ magnitude_bits"

definition
  free_index_update :: "(nat \<Rightarrow> nat) \<Rightarrow> cap \<Rightarrow> cap"
where
  "free_index_update g cap \<equiv>
   case cap of UntypedCap dev ref sz f \<Rightarrow> UntypedCap dev ref sz (g f) | _ \<Rightarrow> cap"

primrec (nonexhaustive)
  untyped_sz_bits :: "cap \<Rightarrow> nat"
where
  "untyped_sz_bits (UntypedCap dev ref sz f) = sz"

abbreviation
  max_free_index_update :: "cap \<Rightarrow> cap"
where
  "max_free_index_update cap \<equiv> cap \<lparr> free_index:= max_free_index (untyped_sz_bits cap) \<rparr>"

definition
  set_untyped_cap_as_full :: "cap \<Rightarrow> cap \<Rightarrow> obj_ref \<times> bool list \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_untyped_cap_as_full src_cap new_cap src_slot \<equiv>
   if (is_untyped_cap src_cap \<and> is_untyped_cap new_cap
       \<and> obj_ref_of src_cap = obj_ref_of new_cap \<and> cap_bits_untyped src_cap = cap_bits_untyped new_cap)
       then set_cap (max_free_index_update src_cap) src_slot else return ()"

text {* Derive a cap into a form in which it can be copied. For internal reasons
not all capability types can be copied at all times and not all capability types
can be copied unchanged. *}
definition
derive_cap :: "cslot_ptr \<Rightarrow> cap \<Rightarrow> (cap,'z::state_ext) se_monad" where
"derive_cap slot cap \<equiv>
 case cap of
    ArchObjectCap c \<Rightarrow> liftME ArchObjectCap $ arch_derive_cap c
    | UntypedCap dev ptr sz f \<Rightarrow> doE ensure_no_children slot; returnOk cap odE
    | Zombie ptr n sz \<Rightarrow> returnOk NullCap
    | IRQControlCap \<Rightarrow> returnOk NullCap
    | _ \<Rightarrow> returnOk cap"

text {* Transform a capability on request from a user thread. The user-supplied
argument word is interpreted differently for different cap types. If the
preserve flag is set this transformation is being done in-place which means some
changes are disallowed because they would invalidate existing CDT relationships.
*}
definition
  update_cap_data :: "bool \<Rightarrow> data \<Rightarrow> cap \<Rightarrow> cap" where
"update_cap_data preserve w cap \<equiv>
  if is_ep_cap cap then
    if cap_ep_badge cap = 0 \<and> \<not> preserve then
      badge_update w cap
    else NullCap
  else if is_ntfn_cap cap then
    if cap_ep_badge cap = 0 \<and> \<not> preserve then
      badge_update w cap
    else NullCap
  else if is_cnode_cap cap then
    let
        (oref, bits, guard) = the_cnode_cap cap;
        (guard_size', guard'') = update_cnode_cap_data w;
        guard' = drop (size guard'' - guard_size') (to_bl guard'')
    in
        if guard_size' + bits > word_bits
        then NullCap
        else CNodeCap oref bits guard'
  else if is_arch_cap cap then
    arch_update_cap_data w (the_arch_cap cap)
  else
    cap"

section {* Resolving capability references *}

text {*
Recursively looks up a capability address to a CNode slot by walking over
multiple CNodes until all the bits in the address are used or there are
no further CNodes.
*}
function resolve_address_bits' :: "'z itself \<Rightarrow> cap \<times> cap_ref \<Rightarrow> (cslot_ptr \<times> cap_ref,'z::state_ext) lf_monad"
where
  "resolve_address_bits' z (cap, cref) =
  (case cap of
     CNodeCap oref radix_bits guard  \<Rightarrow>
     if radix_bits + size guard = 0 then
       fail (* nothing is translated: table broken *)
     else doE
       whenE (\<not> guard \<le> cref)
             (* guard does not match *)
             (throwError $ GuardMismatch (size cref) guard);

       whenE (size cref < radix_bits + size guard)
             (* not enough bits to resolve: table malformed *)
             (throwError $ DepthMismatch (size cref) (radix_bits+size guard));

       offset \<leftarrow> returnOk $ take radix_bits (drop (size guard) cref);
       rest \<leftarrow> returnOk $ drop (radix_bits + size guard) cref;
       if rest = [] then
         returnOk ((oref,offset), [])
       else doE
         next_cap \<leftarrow> liftE $ get_cap (oref, offset);
         if is_cnode_cap next_cap then
           resolve_address_bits' z (next_cap, rest)
         else
           returnOk ((oref,offset), rest)
       odE
     odE
   | _ \<Rightarrow> throwError InvalidRoot)"
  by auto

lemma rab_termination:
  "\<forall>cref guard radix_bits.
    \<not> length cref \<le> radix_bits + length guard \<and>
    (0 < radix_bits \<or> guard \<noteq> []) \<longrightarrow>
      length cref - (radix_bits + length guard) < length cref"
  apply clarsimp
  apply (erule disjE)
   apply arith
  apply (clarsimp simp: neq_Nil_conv)
  apply arith
  done

termination
  apply (relation "measure (\<lambda>(z,cap, cs). size cs)")
  apply (auto simp: whenE_def returnOk_def return_def rab_termination)
  done

definition resolve_address_bits where
"resolve_address_bits \<equiv> resolve_address_bits' TYPE('z::state_ext)"

text {* Specialisations of the capability lookup process to various standard
cases. *}
definition
  lookup_slot_for_thread :: "obj_ref \<Rightarrow> cap_ref \<Rightarrow> (cslot_ptr \<times> cap_ref,'z::state_ext) lf_monad"
where
  "lookup_slot_for_thread thread cref \<equiv> doE
     tcb \<leftarrow> liftE $ gets_the $ get_tcb thread;
     resolve_address_bits (tcb_ctable tcb, cref)
  odE"

definition
  lookup_cap_and_slot :: "obj_ref \<Rightarrow> cap_ref \<Rightarrow> (cap \<times> cslot_ptr,'z::state_ext) lf_monad" where
  "lookup_cap_and_slot thread cptr \<equiv> doE
      (slot, cr) \<leftarrow> lookup_slot_for_thread thread cptr;
      cap \<leftarrow> liftE $ get_cap slot;
      returnOk (cap, slot)
  odE"

definition
  lookup_cap :: "obj_ref \<Rightarrow> cap_ref \<Rightarrow> (cap,'z::state_ext) lf_monad" where
  "lookup_cap thread ref \<equiv> doE
     (ref', _) \<leftarrow> lookup_slot_for_thread thread ref;
     liftE $ get_cap ref'
   odE"

definition
  lookup_slot_for_cnode_op ::
  "bool \<Rightarrow> cap \<Rightarrow> cap_ref \<Rightarrow> nat \<Rightarrow> (cslot_ptr,'z::state_ext) se_monad"
where
 "lookup_slot_for_cnode_op is_source croot ptr depth \<equiv>
  if is_cnode_cap croot then
  doE
    whenE (depth < 1 \<or> depth > word_bits)
      $ throwError (RangeError 1 (of_nat word_bits));
    lookup_error_on_failure is_source $ doE
      ptrbits_for_depth \<leftarrow> returnOk $ drop (length ptr - depth) ptr;
      (slot, rem) \<leftarrow> resolve_address_bits (croot, ptrbits_for_depth);
      case rem of
        [] \<Rightarrow> returnOk slot
      | _  \<Rightarrow> throwError $ DepthMismatch (length rem) 0
    odE
  odE
  else
    throwError (FailedLookup is_source InvalidRoot)"

definition
  lookup_source_slot :: "cap \<Rightarrow> cap_ref \<Rightarrow> nat \<Rightarrow> (cslot_ptr,'z::state_ext) se_monad"
where
 "lookup_source_slot \<equiv> lookup_slot_for_cnode_op True"

definition
  lookup_target_slot :: "cap \<Rightarrow> cap_ref \<Rightarrow> nat \<Rightarrow> (cslot_ptr,'z::state_ext) se_monad"
where
 "lookup_target_slot \<equiv> lookup_slot_for_cnode_op False"

definition
  lookup_pivot_slot :: "cap \<Rightarrow> cap_ref \<Rightarrow> nat \<Rightarrow> (cslot_ptr,'z::state_ext) se_monad"
where
 "lookup_pivot_slot  \<equiv> lookup_slot_for_cnode_op True"


section {* Transferring capabilities *}

text {* These functions are used in interpreting from user arguments the manner
in which a capability transfer should take place. *}

record captransfer =
  ct_receive_root :: cap_ref
  ct_receive_index :: cap_ref
  ct_receive_depth :: data


definition
  captransfer_size :: "nat" -- "in words"
where
  "captransfer_size \<equiv> 3"

definition
  captransfer_from_words :: "machine_word \<Rightarrow> (captransfer,'z::state_ext) s_monad"
where
  "captransfer_from_words ptr \<equiv> do
     w0 \<leftarrow> do_machine_op $ loadWord ptr;
     w1 \<leftarrow> do_machine_op $ loadWord (ptr + word_size);
     w2 \<leftarrow> do_machine_op $ loadWord (ptr + 2 * word_size);
     return \<lparr> ct_receive_root = data_to_cptr w0,
              ct_receive_index = data_to_cptr w1,
              ct_receive_depth = w2 \<rparr>
   od"


definition
  load_cap_transfer :: "obj_ref \<Rightarrow> (captransfer,'z::state_ext) s_monad" where
 "load_cap_transfer buffer \<equiv> do
     offset \<leftarrow> return $ msg_max_length + msg_max_extra_caps + 2;
     captransfer_from_words (buffer + of_nat offset * word_size)
  od"

fun
  get_receive_slots :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                         (cslot_ptr list,'z::state_ext) s_monad"
where
  "get_receive_slots thread (Some buffer) = do
     ct \<leftarrow> load_cap_transfer buffer;

     empty_on_failure $ doE
       cnode \<leftarrow> unify_failure $
                  lookup_cap thread (ct_receive_root ct);
       slot \<leftarrow> unify_failure $ lookup_target_slot cnode
                  (ct_receive_index ct) (unat (ct_receive_depth ct));

       cap \<leftarrow> liftE $ get_cap slot;

       whenE (cap \<noteq> NullCap) (throwError ());

       returnOk [slot]
     odE
   od"
|  "get_receive_slots x None = return []"

text {* Finalise a capability if the capability is known to be of the kind
which can be finalised immediately. This is a simplified version of the
@{text finalise_cap} operation. *}
fun
  fast_finalise :: "cap \<Rightarrow> bool \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "fast_finalise NullCap                 final = return ()"
| "fast_finalise (ReplyCap r)            final =
      (when final $ do
          reply \<leftarrow> get_reply r;
          tptr \<leftarrow> return (reply_tcb reply);
          when (tptr \<noteq> None) $ reply_clear_tcb r
           od)"
| "fast_finalise (EndpointCap r b R)     final =
      (when final $ cancel_all_ipc r)"
| "fast_finalise (NotificationCap r b R) final =
      (when final $ do
          sched_context_maybe_unbind_ntfn r;
          unbind_maybe_notification r;
          cancel_all_signals r
       od)"
| "fast_finalise (SchedContextCap sc b)    final =
      (when final $ do
          sched_context_unbind_all_tcbs sc;
          sched_context_unbind_ntfn sc;
          sched_context_clear_replies sc;
          sched_context_unbind_yield_from sc
      od)"
| "fast_finalise _ _ = fail"

text {* Delete a capability with the assumption that the fast finalisation
process will be sufficient. *}
definition
  cap_delete_one :: "cslot_ptr \<Rightarrow> (unit, 'z::state_ext) s_monad" where
 "cap_delete_one slot \<equiv> do
    cap \<leftarrow> get_cap slot;
    unless (cap = NullCap) $ do
      final \<leftarrow> is_final_cap cap;
      fast_finalise cap final;
      empty_slot slot NullCap
    od
  od"

section {* Revoking and deleting capabilities *}

text {* Deletion of the final capability to any object is a long running
operation if the capability is of these types. *}
definition
  long_running_delete :: "cap \<Rightarrow> bool" where
 "long_running_delete cap \<equiv> case cap of
    CNodeCap ptr bits gd \<Rightarrow> True
  | Zombie ptr bits n \<Rightarrow> True
  | ThreadCap ptr \<Rightarrow> True
  | _ \<Rightarrow> False"


definition
  slot_cap_long_running_delete :: "cslot_ptr \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "slot_cap_long_running_delete slot \<equiv> do
     cap \<leftarrow> get_cap slot;
     case cap of
         NullCap \<Rightarrow> return False
       | _ \<Rightarrow> do
           final \<leftarrow> is_final_cap cap;
           return (final \<and> long_running_delete cap)
         od
   od"

text {* Swap the contents of two capability slots. The capability parameters are
the new states of the capabilities, as the user may request that the
capabilities are transformed as they are swapped. *}
definition
  cap_swap :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cap_swap cap1 slot1 cap2 slot2 \<equiv>
  do
    set_cap cap2 slot1;
    set_cap cap1 slot2;
    slot1_p \<leftarrow> gets (\<lambda>s. cdt s slot1);
    slot2_p \<leftarrow> gets (\<lambda>s. cdt s slot2);
    cdt \<leftarrow> gets cdt;
    (* update children: *)
    cdt' \<leftarrow> return (\<lambda>n. if cdt n = Some slot1
                        then Some slot2
                        else if cdt n = Some slot2
                        then Some slot1
                        else cdt n);
    (* update parents: *)
    set_cdt (cdt' (slot1 := cdt' slot2, slot2 := cdt' slot1));
    do_extended_op (cap_swap_ext slot1 slot2 slot1_p slot2_p);
    is_original \<leftarrow> gets is_original_cap;
    set_original slot1 (is_original slot2);
    set_original slot2 (is_original slot1)
  od"

text {* Move a capability from one slot to another. Once again the new
capability is a parameter as it may be transformed while it is moved. *}
definition
  cap_move :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cap_move new_cap src_slot dest_slot \<equiv> do
    set_cap new_cap dest_slot;
    set_cap NullCap src_slot;
    src_p \<leftarrow> gets (\<lambda>s. cdt s src_slot);
    dest_p \<leftarrow> gets (\<lambda>s. cdt s dest_slot);
    cdt \<leftarrow> gets cdt;
    parent \<leftarrow> return $ cdt src_slot;
    cdt' \<leftarrow> return $ cdt(dest_slot := parent, src_slot := None);
    set_cdt (\<lambda>r. if cdt' r = Some src_slot then Some dest_slot else cdt' r);
    do_extended_op (cap_move_ext src_slot dest_slot src_p dest_p);
    is_original \<leftarrow> gets is_original_cap;
    set_original dest_slot (is_original src_slot);
    set_original src_slot False
  od"

text {* This version of capability swap does not change the capabilities that
are swapped, passing the existing capabilities to the more general function. *}
definition
  cap_swap_for_delete :: "cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "cap_swap_for_delete slot1 slot2 \<equiv>
  when (slot1 \<noteq> slot2) $ do
    cap1 \<leftarrow> get_cap slot1;
    cap2 \<leftarrow> get_cap slot2;
    cap_swap cap1 slot1 cap2 slot2
  od"

text {* The type of possible recursive deletes. *}
datatype
  rec_del_call
  = CTEDeleteCall cslot_ptr bool
  | FinaliseSlotCall cslot_ptr bool
  | ReduceZombieCall cap cslot_ptr bool

text {* Locate the nth capability beyond some base capability slot. *}
definition
  locate_slot :: "cslot_ptr \<Rightarrow> nat \<Rightarrow> cslot_ptr" where
 "locate_slot \<equiv> \<lambda>(a, b) n. (a, drop (32 - length b)
                           (to_bl (of_bl b + of_nat n :: word32)))"

text {* Actions to be taken after deleting an IRQ Handler capability. *}
definition
  deleting_irq_handler :: "irq \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
 "deleting_irq_handler irq \<equiv> do
    slot \<leftarrow> get_irq_slot irq;
    cap_delete_one slot
  od"

text {* Actions that must be taken when a capability is deleted. Returns two
capabilities: The first is a capability to be re-inserted into the slot in place
of the deleted capability; in particular, this will be a Zombie if the deletion
requires a long-running operation. The second represents some further
post-deletion action to be performed after the slot is cleared. For example,
an IRQHandlerCap indicates an IRQ to be cleared. Arch capabilities may also be
associated with arch-specific post-deletion actions. For most cases, however,
NullCap is used to indicate that no post-deletion action is required. *}

fun
  finalise_cap :: "cap \<Rightarrow> bool \<Rightarrow> (cap \<times> cap,'z::state_ext) s_monad"
where
  "finalise_cap NullCap                  final = return (NullCap, NullCap)"
| "finalise_cap (UntypedCap dev r bits f)    final = return (NullCap, NullCap)"
| "finalise_cap (ReplyCap r)             final =
      (liftM (K (NullCap, NullCap)) $ when final $ do
         reply \<leftarrow> get_reply r;
         tptr \<leftarrow> return (reply_tcb reply);
         when (tptr \<noteq> None) $ reply_clear_tcb r
       od)"
| "finalise_cap (EndpointCap r b R)      final =
      (liftM (K (NullCap, NullCap)) $ when final $ cancel_all_ipc r)"
| "finalise_cap (NotificationCap r b R) final =
      (liftM (K (NullCap, NullCap)) $ when final $ do
          sched_context_maybe_unbind_ntfn r;
          unbind_maybe_notification r;
          cancel_all_signals r
        od)"
| "finalise_cap (CNodeCap r bits g)  final =
      return (if final then Zombie r (Some bits) (2 ^ bits) else NullCap, NullCap)"
| "finalise_cap (ThreadCap r)            final =
      do (* can be in any thread state *)
         when final $ unbind_notification r;
         when final $ unbind_from_sc r;
         when final $ suspend r; (* suspend sets the TS to Inactive *)
         when final $ prepare_thread_delete r;
         return (if final then (Zombie r None 5) else NullCap, NullCap)
      od"
| "finalise_cap DomainCap                final = return (NullCap, NullCap)"
| "finalise_cap (SchedContextCap sc bits)     final =
      do
         when final $ sched_context_unbind_all_tcbs sc;
         when final $ sched_context_unbind_ntfn sc;
         when final $ sched_context_clear_replies sc;
         when final $ sched_context_unbind_yield_from sc;
         return (NullCap, NullCap)
      od"
| "finalise_cap SchedControlCap          final = return (NullCap, NullCap)"
| "finalise_cap (Zombie r b n)           final =
      do assert final; return (Zombie r b n, NullCap) od"
| "finalise_cap IRQControlCap            final = return (NullCap, NullCap)"
| "finalise_cap (IRQHandlerCap irq)      final = (
       if final then do
         deleting_irq_handler irq;
         return (NullCap, (IRQHandlerCap irq))
       od
       else return (NullCap, NullCap))"
| "finalise_cap (ArchObjectCap a)        final =
      (arch_finalise_cap a final)"

definition
  can_fast_finalise :: "cap \<Rightarrow> bool" where
 "can_fast_finalise cap \<equiv> case cap of
    ReplyCap r \<Rightarrow> True
  | EndpointCap r b R \<Rightarrow> True
  | NotificationCap r b R \<Rightarrow> True
  | SchedContextCap _ _ \<Rightarrow> True
  | NullCap \<Rightarrow> True
  | _ \<Rightarrow> False"

text {* This operation is used to delete a capability when it is known that a
long-running operation is impossible. It is equivalent to calling the regular
finalisation operation. It cannot be defined in that way as doing so
would create a circular definition. *}

lemma fast_finalise_def2:
  "fast_finalise cap final = do
     assert (can_fast_finalise cap);
     result \<leftarrow> finalise_cap cap final;
     assert (result = (NullCap, NullCap))
   od"
  by (cases cap; simp add: liftM_def K_def assert_def
                           whenE_def when_def bind_assoc
                           can_fast_finalise_def)

text {* The finalisation process on a Zombie or Null capability is finished for
all Null capabilities and for Zombies that cover no slots or only the slot they
are currently stored in. *}
fun
  cap_removeable :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> bool"
where
  "cap_removeable NullCap slot = True"
| "cap_removeable (Zombie slot' bits n) slot =
    ((n = 0) \<or> (n = 1 \<and> (slot', replicate (zombie_cte_bits bits) False) = slot))"
| "cap_removeable _ _ = False"

text {* Checks for Zombie capabilities that refer to the CNode or TCB they are
stored in. *}
definition
  cap_cyclic_zombie :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> bool" where
 "cap_cyclic_zombie cap slot \<equiv> case cap of
         Zombie slot' bits n \<Rightarrow> (slot', replicate (zombie_cte_bits bits) False) = slot
       | _ \<Rightarrow> False"

text {* The complete recursive delete operation. *}
function (sequential)
  rec_del :: "rec_del_call \<Rightarrow> (bool * cap,'z::state_ext) p_monad"
where
  "rec_del (CTEDeleteCall slot exposed) s =
 (doE
    (success, cleanup_info) \<leftarrow> rec_del (FinaliseSlotCall slot exposed);
    without_preemption $ when (exposed \<or> success) $ empty_slot slot cleanup_info;
    returnOk undefined
  odE) s"
|
  "rec_del (FinaliseSlotCall slot exposed) s =
 (doE
    cap \<leftarrow> without_preemption $ get_cap slot;
    if (cap = NullCap)
    then returnOk (True, NullCap)
    else (doE
      is_final \<leftarrow> without_preemption $ is_final_cap cap;
      (remainder, cleanup_info) \<leftarrow> without_preemption $ finalise_cap cap is_final;
      if (cap_removeable remainder slot)
      then returnOk (True, cleanup_info)
      else if (cap_cyclic_zombie remainder slot \<and> \<not> exposed)
      then doE
        without_preemption $ set_cap remainder slot;
        returnOk (False, NullCap)
      odE
      else doE
        without_preemption $ set_cap remainder slot;
        rec_del (ReduceZombieCall remainder slot exposed);
        preemption_point;
        rec_del (FinaliseSlotCall slot exposed)
      odE
    odE)
  odE) s"

| "rec_del (ReduceZombieCall (Zombie ptr bits (Suc n)) slot False) s =
 (doE
    cn \<leftarrow> returnOk $ first_cslot_of (Zombie ptr bits (Suc n));
    assertE (cn \<noteq> slot);
    without_preemption $ cap_swap_for_delete cn slot;
    returnOk undefined
  odE) s"
|
 "rec_del (ReduceZombieCall (Zombie ptr bits (Suc n)) slot True) s =
 (doE
    end_slot \<leftarrow> returnOk (ptr, nat_to_cref (zombie_cte_bits bits) n);
    rec_del (CTEDeleteCall end_slot False);
    new_cap \<leftarrow> without_preemption $ get_cap slot;
    if (new_cap = Zombie ptr bits (Suc n))
    then without_preemption $ set_cap (Zombie ptr bits n) slot
    else assertE (new_cap = NullCap \<or>
                  is_zombie new_cap \<and> first_cslot_of new_cap = slot
                   \<and> first_cslot_of (Zombie ptr bits (Suc n)) \<noteq> slot);
    returnOk undefined
  odE) s"
|
 "rec_del (ReduceZombieCall cap slot exposed) s =
  fail s"
  defer
   apply (simp_all cong: if_cong)[528]
  apply (case_tac x)
  apply (case_tac a)
    apply (auto)[2]
  apply (rename_tac cap cslot_ptr bool)
  apply (case_tac cap, safe)
             apply auto[13]
   -- Zombie
   apply (rename_tac obj_ref option nat)
   apply (case_tac bool)
    apply (case_tac nat, auto)[1]
   apply (metis (full_types) nat.exhaust)
  apply simp
  done

text {* Delete a capability by calling the recursive delete operation. *}
definition
  cap_delete :: "cslot_ptr \<Rightarrow> (unit, 'z::state_ext) p_monad" where
 "cap_delete slot \<equiv> doE rec_del (CTEDeleteCall slot True); returnOk () odE"

text {* Prepare the capability in a slot for deletion but do not delete it. *}
definition
  finalise_slot :: "cslot_ptr \<Rightarrow> bool \<Rightarrow> (bool * cap,'z::state_ext) p_monad"
where
  "finalise_slot p e \<equiv> rec_del (FinaliseSlotCall p e)"

text {* Helper functions for the type of recursive delete calls. *}
primrec
  exposed_rdcall :: "rec_del_call \<Rightarrow> bool"
where
  "exposed_rdcall (CTEDeleteCall slot exposed) = exposed"
| "exposed_rdcall (FinaliseSlotCall slot exposed) = exposed"
| "exposed_rdcall (ReduceZombieCall cap slot exposed) = exposed"

primrec
  isCTEDeleteCall :: "rec_del_call \<Rightarrow> bool"
where
  "isCTEDeleteCall (CTEDeleteCall slot exposed) = True"
| "isCTEDeleteCall (FinaliseSlotCall slot exposed) = False"
| "isCTEDeleteCall (ReduceZombieCall cap slot exposed) = False"

primrec
  slot_rdcall :: "rec_del_call \<Rightarrow> cslot_ptr"
where
  "slot_rdcall (CTEDeleteCall slot exposed) = slot"
| "slot_rdcall (FinaliseSlotCall slot exposed) = slot"
| "slot_rdcall (ReduceZombieCall cap slot exposed) = slot"

text {* Revoke the derived capabilities of a given capability, deleting them
all. *}

function cap_revoke :: "cslot_ptr \<Rightarrow> (unit, 'z::state_ext) p_monad"
where
"cap_revoke slot s = (doE
    cap \<leftarrow> without_preemption $ get_cap slot;
    cdt \<leftarrow> without_preemption $ gets cdt;
    descendants \<leftarrow> returnOk $ descendants_of slot cdt;
    whenE (cap \<noteq> NullCap \<and> descendants \<noteq> {}) (doE
      child \<leftarrow> without_preemption $ select_ext (next_revoke_cap slot) descendants;
      cap \<leftarrow> without_preemption $ get_cap child;
      assertE (cap \<noteq> NullCap);
      cap_delete child;
      preemption_point;
      cap_revoke slot
    odE)
odE) s"
by auto

section {* Inserting and moving capabilities *}

definition
  get_badge :: "cap \<Rightarrow> badge option" where
 "get_badge cap \<equiv> case cap of
    NotificationCap oref badge cr \<Rightarrow> Some badge
  | EndpointCap oref badge cr      \<Rightarrow> Some badge
  | _                              \<Rightarrow> None"


definition
  is_physical :: "cap \<Rightarrow> bool" where
  "is_physical cap \<equiv> case cap of
    NullCap \<Rightarrow> False
  | DomainCap \<Rightarrow> False
  | SchedControlCap \<Rightarrow> False
  | IRQControlCap \<Rightarrow> False
  | IRQHandlerCap _ \<Rightarrow> False
  | ArchObjectCap c \<Rightarrow> arch_is_physical c
  | _ \<Rightarrow> True"

fun
  same_region_as :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
  "same_region_as NullCap c' = False"
| "same_region_as (UntypedCap dev r bits free) c' =
    (is_physical c' \<and>
     r \<le> obj_ref_of c' \<and>
     obj_ref_of c' \<le> obj_ref_of c' + obj_size c' - 1 \<and>
     obj_ref_of c' + obj_size c' - 1 \<le> r + (1 << bits) - 1)"
| "same_region_as (EndpointCap r b R) c' =
    (is_ep_cap c' \<and> obj_ref_of c' = r)"
| "same_region_as (NotificationCap r b R) c' =
    (is_ntfn_cap c' \<and> obj_ref_of c' = r)"
| "same_region_as (CNodeCap r bits g) c' =
    (is_cnode_cap c' \<and> obj_ref_of c' = r \<and> bits_of c' = bits)"
| "same_region_as (ReplyCap n) c' = (c' = ReplyCap n)"
| "same_region_as (ThreadCap r) c' =
    (is_thread_cap c' \<and> obj_ref_of c' = r)"
| "same_region_as (SchedContextCap sc n) c' =
    (is_sched_context_cap c' \<and> obj_ref_of c' = sc \<and> bits_of c' = n)"
| "same_region_as SchedControlCap c' =
    (c' = SchedControlCap)"
| "same_region_as (Zombie r b n) c' = False"
| "same_region_as (IRQControlCap) c' =
    (c' = IRQControlCap \<or> (\<exists>n. c' = IRQHandlerCap n))"
| "same_region_as DomainCap c' = (c' = DomainCap)"
| "same_region_as (IRQHandlerCap n) c' =
    (c' = IRQHandlerCap n)"
| "same_region_as (ArchObjectCap a) c' =
    (case c' of ArchObjectCap a' \<Rightarrow> arch_same_region_as a a' | _ \<Rightarrow> False)"

text {* Check whether two capabilities are to the same object. *}
definition
  same_object_as :: "cap \<Rightarrow> cap \<Rightarrow> bool" where
 "same_object_as cp cp' \<equiv>
   (case (cp, cp') of
      (UntypedCap dev r bits free, _) \<Rightarrow> False
    | (IRQControlCap, IRQHandlerCap n) \<Rightarrow> False
    | (ArchObjectCap ac, ArchObjectCap ac') \<Rightarrow> same_aobject_as ac ac'
    | _ \<Rightarrow> same_region_as cp cp')"



text {*
The function @{text "should_be_parent_of"}
checks whether an existing capability should be a parent of
another to-be-inserted capability. The test is the following:
For capability @{term c} to be a parent of capability @{term c'},
@{term c} needs to be the original capability to the object and needs
to cover the same memory region as @{term c'} (i.e.\ cover the same
object). In the case of endpoint capabilities, if @{term c} is a
badged endpoint cap (@{text "badge \<noteq> 0"}), then it should be a parent
of @{text c'} if @{text c'} has the same badge and is itself not an
original badged endpoint cap.

\begin{figure}
\begin{center}
\includegraphics[width=0.8\textwidth]{imgs/CDT}
\end{center}
\caption{Example capability derivation tree.}\label{fig:CDT}
\end{figure}

Figure \ref{fig:CDT} shows an example capability derivation tree that
illustrates a standard scenario: the top level is a large untyped
capability, the second level splits this capability into two regions
covered by their own untyped caps, both are children of the first
level.  The third level on the left is a copy of the level 2 untyped
capability.  Untyped capabilities when copied always create children,
never siblings.  In this scenario, the untyped capability was typed
into two separate objects, creating two capabilities on level 4, both
are the original capability to the respective object, both are
children of the untyped capability they were created from.

 Ordinary original capabilities can have one level of derived capabilities
(created, for instance, by the copy or mint operations). Further copies
of these derived capabilities will create sibling, in this case
remaining on level 5. There is an exception to this scheme for endpoint
capabilities --- they support an additional layer of depth with the
concept of badged and unbadged endpoints. The original endpoint
capability will be unbadged. Using the mint operation, a copy of
the capability with a specific badge can be created. This new, badged
capability to the same object is treated as an original capability
(the ``original badged endpoint capability'') and supports one level
of derived children like other capabilities.
*}
definition
  should_be_parent_of :: "cap \<Rightarrow> bool \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> bool" where
  "should_be_parent_of c original c' original' \<equiv>
   original \<and>
   same_region_as c c' \<and>
   (case c of
      EndpointCap ref badge R \<Rightarrow> badge \<noteq> 0 \<longrightarrow> cap_ep_badge c' = badge \<and> \<not>original'
    | NotificationCap ref badge R \<Rightarrow> badge \<noteq> 0 \<longrightarrow> cap_ep_badge c' = badge \<and> \<not>original'
    | _ \<Rightarrow> True)"


text {* Insert a new capability as either a sibling or child of an
existing capability. The function @{const should_be_parent_of}
determines which it will be.

The term for @{text dest_original} determines if the new capability
should be counted as the original capability to the object. This test
is usually false, apart from the exceptions listed (newly badged
endpoint capabilities, irq handlers, and untyped caps).
*}


definition
  cap_insert :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "cap_insert new_cap src_slot dest_slot \<equiv> do
    src_cap \<leftarrow> get_cap src_slot;

    dest_original \<leftarrow> return (if is_ep_cap new_cap then
                                cap_ep_badge new_cap \<noteq> cap_ep_badge src_cap
                             else if is_ntfn_cap new_cap then
                                cap_ep_badge new_cap \<noteq> cap_ep_badge src_cap
                             else if \<exists>irq. new_cap = IRQHandlerCap irq then
                                src_cap = IRQControlCap
                             else is_untyped_cap new_cap);

    old_cap \<leftarrow> get_cap dest_slot;
    assert (old_cap = NullCap);
    set_untyped_cap_as_full src_cap new_cap src_slot;
    set_cap new_cap dest_slot;

    is_original \<leftarrow> gets is_original_cap;
    src_parent \<leftarrow> return $
       should_be_parent_of src_cap (is_original src_slot) new_cap dest_original;
    src_p \<leftarrow> gets (\<lambda>s. cdt s src_slot);
    dest_p \<leftarrow> gets (\<lambda>s. cdt s dest_slot);
    update_cdt (\<lambda>cdt. cdt (dest_slot := if src_parent
                                        then Some src_slot
                                        else cdt src_slot));
    do_extended_op (cap_insert_ext src_parent src_slot dest_slot src_p dest_p);
    set_original dest_slot dest_original
  od"


definition
  has_cancel_send_rights :: "cap \<Rightarrow> bool" where
  "has_cancel_send_rights cap \<equiv> case cap of
   EndpointCap _ _ R \<Rightarrow> R = all_rights
   | _ \<Rightarrow> False"

text {* Overwrite the capabilities stored in a TCB while preserving the register
set and other fields. *}
definition
  tcb_registers_caps_merge :: "tcb \<Rightarrow> tcb \<Rightarrow> tcb"
where
 "tcb_registers_caps_merge regtcb captcb \<equiv>
  regtcb \<lparr> tcb_ctable := tcb_ctable captcb,
           tcb_vtable := tcb_vtable captcb,
           tcb_ipcframe := tcb_ipcframe captcb \<rparr>"

section {* Invoking CNode capabilities *}

text {* The CNode capability confers authority to various methods
which act on CNodes and the capabilities within them. Copies of
capabilities may be inserted in empty CNode slots by
Insert. Capabilities may be moved to empty slots with Move or swapped
with others in a three way rotate by Rotate. A Reply capability stored
in a thread's last-caller slot may be saved into a regular CNode slot
with Save.  The Revoke, Delete and Recycle methods may also be
invoked on the capabilities stored in the CNode. *}

definition
  invoke_cnode :: "cnode_invocation \<Rightarrow> (unit, 'z::state_ext) p_monad" where
  "invoke_cnode i \<equiv> case i of
    RevokeCall dest_slot \<Rightarrow> cap_revoke dest_slot
  | DeleteCall dest_slot \<Rightarrow> cap_delete dest_slot
  | InsertCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_insert cap src_slot dest_slot
  | MoveCall cap src_slot dest_slot \<Rightarrow>
       without_preemption $ cap_move cap src_slot dest_slot
  | RotateCall cap1 cap2 slot1 slot2 slot3 \<Rightarrow>
       without_preemption $
       if slot1 = slot3 then
         cap_swap cap1 slot1 cap2 slot2
       else
         do cap_move cap2 slot2 slot3; cap_move cap1 slot1 slot2 od
  | CancelBadgedSendsCall (EndpointCap ep b R) \<Rightarrow> 
    without_preemption $ when (b \<noteq> 0) $ cancel_badged_sends ep b
  | CancelBadgedSendsCall _ \<Rightarrow> fail"


section "Cap classification used to define invariants"

datatype capclass =
  PhysicalClass | IRQClass | ASIDMasterClass | NullClass | DomainClass | IOPortClass

end
