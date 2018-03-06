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
Decoding system calls
*)

chapter "Decoding System Calls"

theory Decode_A
imports
  Interrupt_A
  "./$L4V_ARCH/ArchDecode_A"
  "../design/InvocationLabels_H"
begin

context begin interpretation Arch .

requalify_consts
  ArchDefaultExtraRegisters
  check_valid_ipc_buffer
  is_valid_vtable_root
  arch_decode_irq_control_invocation
  arch_data_to_obj_type
  arch_decode_invocation
  arch_check_irq

end


text {*
  This theory includes definitions describing how user arguments are
decoded into invocation structures; these structures are then used
to perform the actual system call (see @{text "perform_invocation"}).
In addition, these definitions check the validity of these arguments,
throwing an error if given an invalid request.

  As such, this theory describes the binary interface between the
user and the kernel, along with the preconditions on each argument.
*}


section "CNode"

text {* This definition decodes CNode invocations. *}

definition
  decode_cnode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (cnode_invocation,'z::state_ext) se_monad"
where
"decode_cnode_invocation label args cap excaps \<equiv> doE
  unlessE (invocation_type label \<in> set [CNodeRevoke .e. CNodeSaveCaller]) $
    throwError IllegalOperation;
  whenE (length args < 2) (throwError TruncatedMessage);
  index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
  bits \<leftarrow> returnOk $ data_to_nat $ args ! 1;
  args \<leftarrow> returnOk $ drop 2 args;
  dest_slot \<leftarrow> lookup_target_slot cap index bits;
  if length args \<ge> 2 \<and> length excaps > 0
        \<and> invocation_type label \<in> set [CNodeCopy .e. CNodeMutate] then
  doE
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 0;
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 1;
    args \<leftarrow> returnOk $ drop 2 args;
    src_root_cap \<leftarrow> returnOk $ excaps ! 0;
    ensure_empty dest_slot;
    src_slot \<leftarrow>
         lookup_source_slot src_root_cap src_index src_depth;
    src_cap \<leftarrow> liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $
         throwError $ FailedLookup True $ MissingCapability src_depth;
    (rights, cap_data, is_move) \<leftarrow> case (invocation_type label, args) of
      (CNodeCopy, rightsWord # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, None, False)
                odE
     | (CNodeMint, rightsWord # capData # _) \<Rightarrow> doE
                    rights \<leftarrow> returnOk $ data_to_rights $ rightsWord;
                    returnOk $ (rights, Some capData, False)
                odE
     | (CNodeMove, _) \<Rightarrow> returnOk (all_rights, None, True)
     | (CNodeMutate, capData # _) \<Rightarrow> returnOk (all_rights, Some capData, True)
     | _ \<Rightarrow> throwError TruncatedMessage;
    src_cap \<leftarrow> returnOk $ mask_cap rights src_cap;
    new_cap \<leftarrow> (if is_move then returnOk else derive_cap src_slot) (case cap_data of
                  Some w \<Rightarrow> update_cap_data is_move w src_cap
                | None \<Rightarrow> src_cap);
    whenE (new_cap = NullCap) $ throwError IllegalOperation;
    returnOk $ (if is_move then MoveCall else InsertCall) new_cap src_slot dest_slot
  odE
  else if invocation_type label = CNodeRevoke then returnOk $ RevokeCall dest_slot
  else if invocation_type label = CNodeDelete then returnOk $ DeleteCall dest_slot
  else if invocation_type label = CNodeSaveCaller then doE
    ensure_empty dest_slot;
    returnOk $ SaveCall dest_slot
  odE
  else if invocation_type label = CNodeCancelBadgedSends then doE
    cap \<leftarrow> liftE $ get_cap dest_slot;
    unlessE (has_cancel_send_rights cap) $ throwError IllegalOperation;
    returnOk $ CancelBadgedSendsCall cap
  odE
  else if invocation_type label = CNodeRotate \<and> length args > 5
          \<and> length excaps > 1 then
  doE
    pivot_new_data \<leftarrow> returnOk $ args ! 0;
    pivot_index \<leftarrow> returnOk $ data_to_cptr $ args ! 1;
    pivot_depth \<leftarrow> returnOk $ data_to_nat $ args ! 2;
    src_new_data \<leftarrow> returnOk $ args ! 3;
    src_index \<leftarrow> returnOk $ data_to_cptr $ args ! 4;
    src_depth \<leftarrow> returnOk $ data_to_nat $ args ! 5;
    pivot_root_cap <- returnOk $ excaps ! 0;
    src_root_cap <- returnOk $ excaps ! 1;

    src_slot <- lookup_source_slot src_root_cap src_index src_depth;
    pivot_slot <- lookup_pivot_slot pivot_root_cap pivot_index pivot_depth;

    whenE (pivot_slot = src_slot \<or> pivot_slot = dest_slot) $
      throwError IllegalOperation;

    unlessE (src_slot = dest_slot) $ ensure_empty dest_slot;

    src_cap <- liftE $ get_cap src_slot;
    whenE (src_cap = NullCap) $
      throwError $ FailedLookup True $ MissingCapability src_depth;

    pivot_cap <- liftE $ get_cap pivot_slot;
    whenE (pivot_cap = NullCap) $
      throwError $ FailedLookup False $ MissingCapability pivot_depth;

    new_src_cap \<leftarrow> returnOk $ update_cap_data True src_new_data src_cap;
    new_pivot_cap \<leftarrow> returnOk $ update_cap_data True pivot_new_data pivot_cap;

    whenE (new_src_cap = NullCap) $ throwError IllegalOperation;
    whenE (new_pivot_cap = NullCap) $ throwError IllegalOperation;

    returnOk $ RotateCall new_src_cap new_pivot_cap src_slot pivot_slot dest_slot
  odE
  else
    throwError TruncatedMessage
odE"

section "Threads"

text {* The definitions in this section decode invocations
on TCBs.
*}

text {* This definition checks whether the first argument is
between the second and third.
*}

definition
  decode_read_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_read_registers data cap \<equiv> case data of
  flags#n#_ \<Rightarrow> doE
    range_check n 1 $ of_nat (length frameRegisters + length gpRegisters);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ ReadRegisters p (flags !! 0) n ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"

definition
  decode_copy_registers :: "data list \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_copy_registers data cap extra_caps \<equiv> case data of
  flags#_ \<Rightarrow>  doE
    suspend_source \<leftarrow> returnOk (flags !! 0);
    resume_target \<leftarrow> returnOk (flags !! 1);
    transfer_frame \<leftarrow> returnOk (flags !! 2);
    transfer_integer \<leftarrow> returnOk (flags !! 3);
    whenE (extra_caps = []) $ throwError TruncatedMessage;
    src_tcb \<leftarrow> (case extra_caps of
      ThreadCap p # _ \<Rightarrow> returnOk p
    | _ \<Rightarrow> throwError $ InvalidCapability 1);
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    returnOk $ CopyRegisters p src_tcb
                             suspend_source resume_target
                             transfer_frame transfer_integer
                             ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow>  throwError TruncatedMessage"


definition
  decode_write_registers :: "data list \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_write_registers data cap \<equiv> case data of
  flags#n#values \<Rightarrow> doE
    whenE (length values < unat n) $ throwError TruncatedMessage;
    p \<leftarrow> case cap of ThreadCap p \<Rightarrow> returnOk p;
    self \<leftarrow> liftE $ gets cur_thread;
    whenE (p = self) $ throwError IllegalOperation;
    returnOk $ WriteRegisters p (flags !! 0)
               (take (unat n) values) ArchDefaultExtraRegisters
  odE
| _ \<Rightarrow> throwError TruncatedMessage"


definition
  check_prio :: "data \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) se_monad"
where
  "check_prio new_prio auth_tcb \<equiv>
    doE
      mcp \<leftarrow> liftE $ thread_get tcb_mcpriority auth_tcb;
      whenE (new_prio > ucast mcp) $ throwError (RangeError 0 (ucast mcp))
    odE"


definition
  decode_set_priority :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_priority args cap slot extra_caps \<equiv> doE
     whenE (length args = 0 \<or> length extra_caps = 0) $ throwError TruncatedMessage;
     prio \<leftarrow> returnOk $ ucast (args ! 0);
     auth_tcb \<leftarrow> case fst (extra_caps ! 0) of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     returnOk (ThreadControl (obj_ref_of cap) slot None None
                             (Some (prio, auth_tcb)) None None None None)
     odE"


definition
  decode_set_mcpriority :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_mcpriority args cap slot extra_caps \<equiv> doE
     whenE (length args = 0 \<or> length extra_caps = 0) $ throwError TruncatedMessage;
     new_mcp \<leftarrow> returnOk $ ucast $ args ! 0;
     auth_tcb \<leftarrow> case fst (extra_caps ! 0) of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     returnOk (ThreadControl (obj_ref_of cap) slot None (Some (new_mcp, auth_tcb))
                             None None None None None)
     odE"


definition
  decode_set_sched_params :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_sched_params args cap slot extra_caps \<equiv> doE
     whenE (length args < 2) $ throwError TruncatedMessage;
     whenE (length extra_caps = 0) $ throwError TruncatedMessage;
     new_mcp \<leftarrow> returnOk $ ucast $ args ! 0;
     new_prio \<leftarrow> returnOk $ ucast $ args ! 1;
     auth_tcb \<leftarrow> case fst (extra_caps ! 0) of
         ThreadCap tcb_ptr \<Rightarrow> returnOk tcb_ptr
       | _ \<Rightarrow> throwError (InvalidCapability 1);
     check_prio (args ! 0) auth_tcb;
     check_prio (args ! 1) auth_tcb;
     returnOk (ThreadControl (obj_ref_of cap) slot None
                             (Some (new_mcp, auth_tcb)) (Some (new_prio, auth_tcb)) None None None None)
     odE"


definition
  decode_set_ipc_buffer ::
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
"decode_set_ipc_buffer args cap slot excs \<equiv> doE
  whenE (length args = 0) $ throwError TruncatedMessage;
  whenE (length excs = 0) $ throwError TruncatedMessage;
  buffer \<leftarrow> returnOk $ data_to_vref $ args ! 0;
  (bcap, bslot) \<leftarrow> returnOk $ excs ! 0;
  newbuf \<leftarrow> if buffer = 0 then returnOk None
           else doE
      buffer_cap \<leftarrow> derive_cap bslot bcap;
      check_valid_ipc_buffer buffer buffer_cap;
      returnOk $ Some (buffer_cap, bslot)
    odE;
  returnOk $ 
    ThreadControl (obj_ref_of cap) slot None None None None None (Some (buffer, newbuf)) None
odE"


definition
  decode_set_space
  :: "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_set_space args cap slot excaps \<equiv> doE
   whenE (length args < 3 \<or> length excaps < 2) $ throwError TruncatedMessage;
   fault_ep \<leftarrow> returnOk $ args ! 0;
   croot_data  \<leftarrow> returnOk $ args ! 1;
   vroot_data  \<leftarrow> returnOk $ args ! 2;
   croot_arg  \<leftarrow> returnOk $ excaps ! 0;
   vroot_arg  \<leftarrow> returnOk $ excaps ! 1;
   can_chg_cr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_ctable_ptr $ obj_ref_of cap;
   can_chg_vr \<leftarrow> liftE $ liftM Not $ slot_cap_long_running_delete
                      $ get_tcb_vtable_ptr $ obj_ref_of cap;
   unlessE (can_chg_cr \<and> can_chg_vr) $ throwError IllegalOperation;

   croot_cap  \<leftarrow> returnOk $ fst croot_arg;
   croot_slot \<leftarrow> returnOk $ snd croot_arg;
   croot_cap' \<leftarrow> derive_cap croot_slot $
                   (if croot_data = 0 then id else update_cap_data False croot_data)
                   croot_cap;
   unlessE (is_cnode_cap croot_cap') $ throwError IllegalOperation;
   croot \<leftarrow> returnOk (croot_cap', croot_slot);

   vroot_cap  \<leftarrow> returnOk $ fst vroot_arg;
   vroot_slot \<leftarrow> returnOk $ snd vroot_arg;
   vroot_cap' \<leftarrow> derive_cap vroot_slot $
                   (if vroot_data = 0 then id else update_cap_data False vroot_data)
                   vroot_cap;
   unlessE (is_valid_vtable_root vroot_cap') $ throwError IllegalOperation;
   vroot \<leftarrow> returnOk (vroot_cap', vroot_slot);

   returnOk $ ThreadControl (obj_ref_of cap) slot (Some (to_bl fault_ep)) None None
                            (Some croot) (Some vroot) None None
 odE"

definition
  decode_udpate_sc :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_udpate_sc cap slot sc_cap \<equiv>
    if sc_cap = NullCap then
      returnOk $ ThreadControl (obj_ref_of cap) slot None None None None None None (Some None)
    else doE
      tcb_ptr \<leftarrow> returnOk $ obj_ref_of cap;
      unlessE (is_sched_context_cap sc_cap) $ throwError (InvalidCapability 0);
      sc_ptr \<leftarrow> returnOk $ obj_ref_of sc_cap;
      sc_ptr' \<leftarrow> liftE $ thread_get tcb_sched_context tcb_ptr;
      whenE (sc_ptr' \<noteq> None \<and> sc_ptr' \<noteq> Some sc_ptr) $ throwError IllegalOperation;
      sc \<leftarrow> liftE $ get_sched_context sc_ptr;
      whenE (sc_tcb sc \<noteq> None \<and> sc_tcb sc \<noteq> Some tcb_ptr) $ throwError IllegalOperation;
      returnOk $ ThreadControl tcb_ptr slot None None None None None None (Some (Some sc_ptr))
    odE"

definition
  decode_tcb_configure ::
  "data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_tcb_configure args cap slot extra_caps \<equiv> doE
     whenE (length args < 4) $ throwError TruncatedMessage;
     whenE (length extra_caps < 4) $ throwError TruncatedMessage;
     fault_ep \<leftarrow> returnOk $ args ! 0;
     croot_data \<leftarrow> returnOk $ args ! 1;
     vroot_data \<leftarrow> returnOk $ args ! 2;
     sc_cap \<leftarrow> returnOk $ fst (hd extra_caps);
     crootvroot \<leftarrow> returnOk $ take 2 (drop 1 extra_caps);
     buffer_cap \<leftarrow> returnOk $ extra_caps ! 3;
     buffer \<leftarrow> returnOk $ args ! 3;
     set_params \<leftarrow> decode_set_ipc_buffer [buffer] cap slot [buffer_cap];
     set_space \<leftarrow> decode_set_space [fault_ep, croot_data, vroot_data] cap slot crootvroot;
     update_sc \<leftarrow> decode_udpate_sc cap slot sc_cap;
     returnOk $ ThreadControl (obj_ref_of cap) slot (tc_new_fault_ep set_space)
                              None None
                              (tc_new_croot set_space) (tc_new_vroot set_space)
                              (tc_new_buffer set_params) (tc_new_sc update_sc)
   odE" 

definition
  decode_bind_notification ::
  "cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_bind_notification cap extra_caps \<equiv> case cap of
    ThreadCap tcb \<Rightarrow> doE
     whenE (length extra_caps = 0) $ throwError TruncatedMessage;
     nTFN \<leftarrow> liftE $ get_bound_notification tcb;
     case nTFN of
         Some _ \<Rightarrow> throwError IllegalOperation
       | None \<Rightarrow> returnOk ();
     (ntfnptr, rights) \<leftarrow> case fst (hd extra_caps) of
         NotificationCap ptr _ r \<Rightarrow> returnOk (ptr, r)
       | _ \<Rightarrow> throwError IllegalOperation;
     whenE (AllowRecv \<notin> rights) $ throwError IllegalOperation;
     ntfn \<leftarrow> liftE  $ get_notification ntfnptr;
     case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
         (IdleNtfn, None) \<Rightarrow> returnOk ()
       | (ActiveNtfn _, None) \<Rightarrow> returnOk ()
       | _ \<Rightarrow> throwError IllegalOperation;
      returnOk $ NotificationControl tcb (Some ntfnptr)
   odE
 | _ \<Rightarrow> throwError IllegalOperation"


definition
  decode_unbind_notification :: "cap \<Rightarrow> (tcb_invocation,'z::state_ext) se_monad"
where
  "decode_unbind_notification cap \<equiv> case cap of
     ThreadCap tcb \<Rightarrow> doE
       nTFN \<leftarrow> liftE $ get_bound_notification tcb;
       case nTFN of
           None \<Rightarrow> throwError IllegalOperation
         | Some _ \<Rightarrow> returnOk ();
       returnOk $ NotificationControl tcb None
    odE
 | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_tcb_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap \<Rightarrow> cslot_ptr \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
  (tcb_invocation,'z::state_ext) se_monad"
where
 "decode_tcb_invocation label args cap slot excs \<equiv>
  case invocation_type label of
      TCBReadRegisters \<Rightarrow> decode_read_registers args cap
    | TCBWriteRegisters \<Rightarrow> decode_write_registers args cap
    | TCBCopyRegisters \<Rightarrow> decode_copy_registers args cap $ map fst excs
    | TCBSuspend \<Rightarrow> returnOk $ Suspend $ obj_ref_of cap
    | TCBResume \<Rightarrow> returnOk $ Resume $ obj_ref_of cap
    | TCBConfigure \<Rightarrow> decode_tcb_configure args cap slot excs
    | TCBSetPriority \<Rightarrow> decode_set_priority args cap slot excs
    | TCBSetMCPriority \<Rightarrow> decode_set_mcpriority args cap slot excs
    | TCBSetSchedParams \<Rightarrow> decode_set_sched_params args cap slot excs
    | TCBSetIPCBuffer \<Rightarrow> decode_set_ipc_buffer args cap slot excs
    | TCBSetSpace \<Rightarrow> decode_set_space args cap slot excs
    | TCBBindNotification \<Rightarrow> decode_bind_notification cap excs
    | TCBUnbindNotification \<Rightarrow> decode_unbind_notification cap
    | _ \<Rightarrow> throwError IllegalOperation"

definition
  decode_domain_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
    ((obj_ref \<times> domain), 'z::state_ext) se_monad"
where
  "decode_domain_invocation label args excs \<equiv> doE
     whenE (invocation_type label \<noteq> DomainSetSet) $ throwError IllegalOperation;
     domain \<leftarrow> (case args of
       x # xs \<Rightarrow> doE
         whenE (unat x \<ge> num_domains) $ throwError $ InvalidArgument 0;
         returnOk (ucast x)
       odE
       | _ \<Rightarrow> throwError TruncatedMessage);
     whenE (length excs = 0) $ throwError TruncatedMessage;
     case (fst (hd excs)) of ThreadCap ptr \<Rightarrow> returnOk $ (ptr, domain)
       | _ \<Rightarrow> throwError $ InvalidArgument 1
   odE"

section "Scheduling Contexts"

text {* The following definitions decode system calls related to scheduling contexts
and scheduling control. *}

definition
  decode_sched_context_invocation :: 
  "data \<Rightarrow> obj_ref \<Rightarrow> cap list \<Rightarrow> (sched_context_invocation,'z::state_ext) se_monad"
where
  "decode_sched_context_invocation label sc_ptr excaps \<equiv>
  case invocation_type label of
    SchedContextBind \<Rightarrow> doE
      whenE (length excaps = 0) $ throwError TruncatedMessage;
      cap \<leftarrow> returnOk $ hd excaps;
      sc \<leftarrow> liftE $ get_sched_context sc_ptr;
      whenE (sc_tcb sc \<noteq> None) $ throwError IllegalOperation;
      whenE (\<not>is_thread_cap cap) $ throwError (InvalidCapability 1);
      tcb_ptr \<leftarrow> returnOk $ obj_ref_of cap;
      sc_ptr_opt \<leftarrow> liftE $ thread_get tcb_sched_context tcb_ptr;
      whenE (sc_ptr_opt \<noteq> None) $ throwError IllegalOperation;
      returnOk $ InvokeSchedContextBind sc_ptr tcb_ptr
    odE
  | SchedContextUnbindObject \<Rightarrow> doE
      whenE (length excaps = 0) $ throwError TruncatedMessage;
      cap \<leftarrow> returnOk $ hd excaps;
      whenE (\<not>is_thread_cap cap) $ throwError (InvalidCapability 1);
      tcb_ptr \<leftarrow> returnOk $ obj_ref_of cap;
      sc_ptr_opt \<leftarrow> liftE $ thread_get tcb_sched_context tcb_ptr;
      whenE (Some sc_ptr \<noteq> sc_ptr_opt) $ throwError IllegalOperation;
      returnOk $ InvokeSchedContextUnbindObject sc_ptr
    odE
  | SchedContextUnbind \<Rightarrow> returnOk $ InvokeSchedContextUnbind sc_ptr
  | _ \<Rightarrow> throwError $ IllegalOperation"


definition
  TIME_ARG_SIZE :: nat
where
  "TIME_ARG_SIZE \<equiv> 2" (* sizeof(ticks_t) / sizeof(word_t) *)

definition
  parse_time_arg :: "nat \<Rightarrow> data list \<Rightarrow> ticks"
where
  "parse_time_arg i args \<equiv> (ucast (args!(i+1)) << 32) + ucast (args!i)"

definition
  decode_sched_control_invocation :: 
  "data \<Rightarrow> data list \<Rightarrow> cap list \<Rightarrow> (sched_control_invocation,'z::state_ext) se_monad"
where
  "decode_sched_control_invocation label args excaps \<equiv> doE
    unlessE (invocation_type label = SchedControlConfigure) $ throwError IllegalOperation;
    whenE (length excaps = 0) $ throwError TruncatedMessage;
    whenE (length args < TIME_ARG_SIZE*2 + 1) $ throwError TruncatedMessage;
    budget_\<mu>s \<leftarrow> returnOk $ parse_time_arg 0 args;
    period_\<mu>s \<leftarrow> returnOk $ parse_time_arg TIME_ARG_SIZE args;
    max_refills \<leftarrow> returnOk $ args ! (2 * TIME_ARG_SIZE);
    target_cap \<leftarrow> returnOk $ hd excaps;
    whenE (\<not>is_sched_context_cap target_cap) $ throwError (InvalidCapability 1);
    sc_ptr \<leftarrow> returnOk $ obj_ref_of target_cap;
    whenE (budget_\<mu>s > maxTimer_us \<or> budget_\<mu>s < MIN_BUDGET_US) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast maxTimer_us));
    whenE (period_\<mu>s > maxTimer_us \<or> period_\<mu>s < MIN_BUDGET_US) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast maxTimer_us));
    whenE (period_\<mu>s < budget_\<mu>s) $
      throwError (RangeError (ucast MIN_BUDGET_US) (ucast period_\<mu>s));
    whenE (MAX_REFILLS < max_refills) $
      throwError (RangeError 0 (of_nat (MAX_REFILLS - MIN_REFILLS - 1)));
    returnOk $ InvokeSchedControlConfigure sc_ptr
                 (us_to_ticks budget_\<mu>s) (us_to_ticks period_\<mu>s) (unat $ max_refills + MIN_REFILLS)
  odE"


section "IRQ"

text {* The following two definitions decode system calls for the
interrupt controller and interrupt handlers *}

definition
  decode_irq_control_invocation :: "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap list
                                     \<Rightarrow> (irq_control_invocation,'z::state_ext) se_monad" where
 "decode_irq_control_invocation label args src_slot cps \<equiv>
  (if invocation_type label = IRQIssueIRQHandler
    then if length args \<ge> 3 \<and> length cps \<ge> 1
      then let irq_word = args ! 0;
               index = args ! 1;
               depth = args ! 2;
               cnode = cps ! 0;
               irq = ucast irq_word
      in doE
        arch_check_irq irq_word;
        irq_active \<leftarrow> liftE $ is_irq_active irq;
        whenE irq_active $ throwError RevokeFirst;

        dest_slot \<leftarrow> lookup_target_slot
               cnode (data_to_cptr index) (unat depth);
        ensure_empty dest_slot;

        returnOk $ IRQControl irq dest_slot src_slot
      odE
    else throwError TruncatedMessage
  else liftME ArchIRQControl $ arch_decode_irq_control_invocation label args src_slot cps)"

definition
  data_to_bool :: "data \<Rightarrow> bool"
where
  "data_to_bool d \<equiv> d \<noteq> 0"

definition
  decode_irq_handler_invocation :: "data \<Rightarrow> irq \<Rightarrow> (cap \<times> cslot_ptr) list
                                     \<Rightarrow> (irq_handler_invocation,'z::state_ext) se_monad" where
 "decode_irq_handler_invocation label irq cps \<equiv>
  if invocation_type label = IRQAckIRQ
    then returnOk $ ACKIrq irq
  else if invocation_type label = IRQSetIRQHandler
    then if cps \<noteq> []
      then let (cap, slot) = hd cps in
      if is_ntfn_cap cap \<and> AllowSend \<in> cap_rights cap
      then returnOk $ SetIRQHandler irq cap slot
      else throwError $ InvalidCapability 0
    else throwError TruncatedMessage
  else if invocation_type label = IRQClearIRQHandler
    then returnOk $ ClearIRQHandler irq
  else throwError IllegalOperation"

section "Untyped"

text {* The definitions in this section deal with decoding invocations
of untyped memory capabilities.
*}

definition
  data_to_obj_type :: "data \<Rightarrow> (apiobject_type,'z::state_ext) se_monad" where
  "data_to_obj_type type \<equiv> doE
    n \<leftarrow> returnOk $ data_to_nat type;
    if n = 0 then
      returnOk $ Untyped
    else if n = 1 then
      returnOk $ TCBObject
    else if n = 2 then
      returnOk $ EndpointObject
    else if n = 3 then
      returnOk $ NotificationObject
    else if n = 4 then
      returnOk $ CapTableObject
    else (case arch_data_to_obj_type (n - 5)
       of Some tp \<Rightarrow> returnOk (ArchObject tp)
        | None \<Rightarrow> throwError (InvalidArgument 0))
  odE"

definition
  decode_untyped_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap list \<Rightarrow> (untyped_invocation,'z::state_ext) se_monad"
where
"decode_untyped_invocation label args slot cap excaps \<equiv> doE
  unlessE (invocation_type label = UntypedRetype) $ throwError IllegalOperation;
  whenE (length args < 6) $ throwError TruncatedMessage;
  whenE (length excaps = 0) $ throwError TruncatedMessage;
  root_cap \<leftarrow> returnOk $ excaps ! 0;
  new_type \<leftarrow> data_to_obj_type (args!0);

  user_obj_size \<leftarrow> returnOk $ data_to_nat (args!1);
  unlessE (user_obj_size \<le> untyped_max_bits)
    $ throwError (RangeError 0 (of_nat untyped_max_bits));
  whenE (new_type = CapTableObject \<and> user_obj_size = 0)
    $ throwError (InvalidArgument 1);
  whenE (new_type = Untyped \<and> user_obj_size < untyped_min_bits)
    $ throwError (InvalidArgument 1);
  node_index \<leftarrow> returnOk $ data_to_cptr (args!2);
  node_depth \<leftarrow> returnOk $ data_to_nat (args!3);

  node_cap \<leftarrow> if node_depth = 0
        then returnOk root_cap
        else doE
            node_slot \<leftarrow> lookup_target_slot
                root_cap node_index node_depth;
            liftE $ get_cap node_slot
        odE;

  if is_cnode_cap node_cap
        then  returnOk ()
        else  throwError $ FailedLookup False $ MissingCapability node_depth;

  node_offset \<leftarrow> returnOk $ data_to_nat (args ! 4);
  node_window \<leftarrow> returnOk $ data_to_nat (args ! 5);
  radix_bits \<leftarrow> returnOk $ bits_of node_cap;
  node_size \<leftarrow> returnOk (2 ^ radix_bits);

  whenE (node_offset < 0 \<or> node_offset > node_size - 1) $
    throwError $ RangeError 0 (of_nat (node_size - 1));

  whenE (node_window < 1 \<or> node_window > 256) $ throwError $ RangeError 1 256;

  whenE (node_window < 1 \<or> node_window > node_size - node_offset) $
    throwError $ RangeError 1 (of_nat (node_size - node_offset));

  oref \<leftarrow> returnOk $ obj_ref_of node_cap;
  offsets \<leftarrow> returnOk $ map (nat_to_cref radix_bits)
                           [node_offset ..< node_offset + node_window];
  slots \<leftarrow> returnOk $ map (\<lambda>cref. (oref, cref)) offsets;

  mapME_x ensure_empty slots;

  reset \<leftarrow> liftE $ const_on_failure False $ (doE
    ensure_no_children slot;
    returnOk True
  odE);

  free_index \<leftarrow> returnOk (if reset then 0 else free_index_of cap);
  free_ref \<leftarrow> returnOk (get_free_ref (obj_ref_of cap) free_index);
  object_size \<leftarrow> returnOk (obj_bits_api new_type user_obj_size);
  aligned_free_ref \<leftarrow> returnOk (alignUp free_ref object_size);
  untyped_free_bytes \<leftarrow> returnOk (obj_size cap - of_nat (free_index));

  max_count \<leftarrow> returnOk ( untyped_free_bytes >> object_size);
  whenE (unat max_count < node_window) $
        throwError $ NotEnoughMemory $ untyped_free_bytes;

  not_frame \<leftarrow> returnOk (\<not> is_frame_type new_type);
  (ptr, is_device) \<leftarrow> case cap of
                        UntypedCap dev p n f \<Rightarrow> returnOk (p,dev)
                      | _ \<Rightarrow> fail;
  whenE (is_device \<and> not_frame \<and> new_type \<noteq> Untyped) $
           throwError $ InvalidArgument 1;
  returnOk $ Retype slot reset ptr aligned_free_ref new_type user_obj_size slots is_device
odE"

section "Toplevel invocation decode."

text {* This definition is the toplevel decoding definition; it dispatches
to the above definitions, after checking, in some cases, whether the
invocation is allowed.
*}

definition
  decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (invocation,'z::state_ext) se_monad"
where
  "decode_invocation label args cap_index slot cap excaps \<equiv>
  case cap of
    EndpointCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeEndpoint ptr badge (AllowGrant \<in> rights)
      else throwError $ InvalidCapability 0
  | NotificationCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeNotification ptr badge
      else throwError $ InvalidCapability 0
  | ReplyCap thread False \<Rightarrow>
      returnOk $ InvokeReply thread slot
  | IRQControlCap \<Rightarrow>
      liftME InvokeIRQControl
        $ decode_irq_control_invocation label args slot (map fst excaps)
  | IRQHandlerCap irq \<Rightarrow>
      liftME InvokeIRQHandler
        $ decode_irq_handler_invocation label irq excaps
  | ThreadCap ptr \<Rightarrow>
      liftME InvokeTCB $ decode_tcb_invocation label args cap slot excaps
  | DomainCap \<Rightarrow>
      liftME (case_prod InvokeDomain) $ decode_domain_invocation label args excaps
  | SchedContextCap sc \<Rightarrow>
      liftME InvokeSchedContext $ decode_sched_context_invocation label sc (map fst excaps)
  | SchedControlCap \<Rightarrow>
      liftME InvokeSchedControl $ decode_sched_control_invocation label args (map fst excaps)
  | CNodeCap ptr bits _ \<Rightarrow>
      liftME InvokeCNode $ decode_cnode_invocation label args cap (map fst excaps)
  | UntypedCap dev ptr sz fi \<Rightarrow>
      liftME InvokeUntyped $ decode_untyped_invocation label args slot cap (map fst excaps)
  | ArchObjectCap arch_cap \<Rightarrow>
      liftME InvokeArchObject $
        arch_decode_invocation label args cap_index slot arch_cap excaps
  | _ \<Rightarrow>
      throwError $ InvalidCapability 0"


end
