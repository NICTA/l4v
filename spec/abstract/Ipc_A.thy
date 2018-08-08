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
Specification of Inter-Process Communication.
*)

chapter "IPC"

theory Ipc_A
imports Tcb_A "./$L4V_ARCH/ArchFault_A"
begin

context begin interpretation Arch .

requalify_consts
  make_arch_fault_msg
  handle_arch_fault_reply
end

section {* Getting and setting the message info register. *}

definition
  get_message_info :: "obj_ref \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "get_message_info thread \<equiv> do
     x \<leftarrow> as_user thread $ get_register msg_info_register;
     return $ data_to_message_info x
   od"

section {* IPC Capability Transfers *}

definition
  remove_rights :: "cap_rights \<Rightarrow> cap \<Rightarrow> cap"
where
 "remove_rights rights cap \<equiv> cap_rights_update (cap_rights cap - rights) cap"

text {* In addition to the data payload a message may also contain capabilities.
When a thread requests additional capabilities be transferred the identities of
those capabilities are retreived from the thread's IPC buffer. *}
definition
  buffer_cptr_index :: nat
where
 "buffer_cptr_index \<equiv> (msg_max_length + 2)"

primrec
  get_extra_cptrs :: "obj_ref option \<Rightarrow> message_info \<Rightarrow> (cap_ref list,'z::state_ext) s_monad"
where
  "get_extra_cptrs (Some buf) mi =
    (liftM (map data_to_cptr) $ mapM (load_word_offs buf)
        [buffer_cptr_index ..< buffer_cptr_index + (unat (mi_extra_caps mi))])"
| "get_extra_cptrs None mi = return []"

definition
  get_extra_cptr :: "obj_ref \<Rightarrow> nat \<Rightarrow> (cap_ref,'z::state_ext) s_monad"
where
  "get_extra_cptr buffer n \<equiv> liftM data_to_cptr
      (load_word_offs buffer (n + buffer_cptr_index))"

text {* This function both looks up the addresses of the additional capabilities
and retreives them from the sender's CSpace. *}
definition
  lookup_extra_caps :: "obj_ref \<Rightarrow> data option \<Rightarrow> message_info \<Rightarrow> ((cap \<times> cslot_ptr) list,'z::state_ext) f_monad" where
  "lookup_extra_caps thread buffer mi \<equiv> doE
       cptrs \<leftarrow> liftE $ get_extra_cptrs buffer mi;
       mapME (\<lambda>cptr. cap_fault_on_failure (of_bl cptr) False $ lookup_cap_and_slot thread cptr) cptrs
  odE"

text {* Capability transfers. Capabilities passed along with a message are split
into two groups. Capabilities to the same endpoint as the message is passed
through are not copied. Their badges are unwrapped and stored in the receiver's
message buffer instead. Other capabilities are copied into the given slots.

Capability unwrapping allows a client to efficiently demonstrate to a server
that it possesses authority to two or more services that server provides.
*}
definition
  set_extra_badge :: "obj_ref \<Rightarrow> machine_word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_extra_badge buffer badge n \<equiv>
      store_word_offs buffer (buffer_cptr_index + n) badge"

type_synonym transfer_caps_data = "(cap \<times> cslot_ptr) list \<times> cslot_ptr list"

fun
  transfer_caps_loop :: "obj_ref option \<Rightarrow> obj_ref \<Rightarrow> nat
                          \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> cslot_ptr list
                          \<Rightarrow> message_info \<Rightarrow> (message_info,'z::state_ext) s_monad"
where
  "transfer_caps_loop ep rcv_buffer n [] slots
      mi = return (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                        (mi_label mi))"
| "transfer_caps_loop ep rcv_buffer n ((cap, slot) # morecaps)
         slots mi =
  const_on_failure (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi)) (doE
    transfer_rest \<leftarrow> returnOk $ transfer_caps_loop ep
         rcv_buffer (n + 1) morecaps;
    if (is_ep_cap cap \<and> ep = Some (obj_ref_of cap))
    then doE
       liftE $ set_extra_badge rcv_buffer (cap_ep_badge cap) n;
       liftE $ transfer_rest slots (MI (mi_length mi) (mi_extra_caps mi)
         (mi_caps_unwrapped mi || (1 << n)) (mi_label mi))
    odE
    else if slots \<noteq> []
    then doE
      cap' \<leftarrow> derive_cap slot cap;
      whenE (cap' = NullCap) $ throwError undefined;
      liftE $ cap_insert cap' slot (hd slots);
      liftE $ transfer_rest (tl slots) mi
    odE
    else returnOk (MI (mi_length mi) (of_nat n) (mi_caps_unwrapped mi)
                       (mi_label mi))
  odE)"

definition
  transfer_caps :: "message_info \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow>
                   obj_ref option \<Rightarrow> obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                   (message_info,'z::state_ext) s_monad"
where
  "transfer_caps info caps endpoint receiver recv_buffer \<equiv> do
     dest_slots \<leftarrow> get_receive_slots receiver recv_buffer;
     mi' \<leftarrow> return $ MI (mi_length info) 0 0 (mi_label info);
     case recv_buffer of
       None \<Rightarrow> return mi'
     | Some receive_buffer \<Rightarrow>
         transfer_caps_loop endpoint receive_buffer 0 caps dest_slots mi'
   od"

section {* Fault Handling *}

text {* Threads fault when they attempt to access services that are not backed
by any resources. Such a thread is then blocked and a fault messages is sent to
its supervisor. When a reply to that message is sent the thread is reactivated.
*}

text {* Format a message for a given fault type. *}
fun
  make_fault_msg :: "fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
  "make_fault_msg (CapFault cptr rp lf) thread = (do
     pc \<leftarrow> as_user thread getRestartPC;
     return (1, pc # cptr # (if rp then 1 else 0) # msg_from_lookup_failure lf)
   od)"
| "make_fault_msg (UnknownSyscallException n) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister syscallMessage;
     return (2, msg @ [n])
   od)"
| "make_fault_msg (UserException exception code) thread = (do
     msg \<leftarrow> as_user thread $ mapM getRegister exceptionMessage;
     return (3, msg @ [exception, code])
   od)"
| "make_fault_msg (Timeout badge) thread = (do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     case (tcb_sched_context tcb) of None \<Rightarrow> return (5, [badge])
     | Some sc \<Rightarrow> do
         consumed \<leftarrow> sched_context_update_consumed sc;
         return (5, badge # (ucast consumed) # [ucast (consumed >> 32)])
       od
   od)"
| "make_fault_msg (ArchFault af) thread = make_arch_fault_msg af thread " (* arch_fault *)

text {* React to a fault reply. The reply message is interpreted in a manner
that depends on the type of the original fault. For some fault types a thread
reconfiguration is performed. This is done entirely to save the fault message
recipient an additional system call. This function returns a boolean indicating
whether the thread should now be restarted. *}
fun
  handle_fault_reply :: "fault \<Rightarrow> obj_ref \<Rightarrow>
                         data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_fault_reply (CapFault cptr rp lf) thread x y = return True"
| "handle_fault_reply (UnknownSyscallException n) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. set_register r $ sanitise_register t r v)
         syscallMessage msg;
     return (label = 0)
   od"
| "handle_fault_reply (UserException exception code) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. set_register r $ sanitise_register t r v)
         exceptionMessage msg;
     return (label = 0)
   od"
| "handle_fault_reply (Timeout badge) thread label msg = do
     t \<leftarrow> arch_get_sanitise_register_info thread;
     as_user thread $ zipWithM_x
         (\<lambda>r v. set_register r $ sanitise_register t r v)
         timeoutMessage msg;
     return (label = 0)
   od"
| " handle_fault_reply (ArchFault af) thread label msg =
    handle_arch_fault_reply af thread label msg" (* arch_fault *)

text {* Transfer a fault message from a faulting thread to its supervisor. *}
definition
  do_fault_transfer :: "data \<Rightarrow> obj_ref \<Rightarrow> obj_ref
                             \<Rightarrow> obj_ref option \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_fault_transfer badge sender receiver buf \<equiv> do
    fault \<leftarrow> thread_get tcb_fault sender;
    f \<leftarrow> (case fault of
         Some f \<Rightarrow> return f
       | None \<Rightarrow> fail);
    (label, msg) \<leftarrow> make_fault_msg f sender;
    sent \<leftarrow> set_mrs receiver buf msg;
    set_message_info receiver $ MI sent 0 0 label;
    as_user receiver $ set_register badge_register badge
  od"

section {* Synchronous Message Transfers *}

text {* Transfer a non-fault message. *}
definition
  do_normal_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option
                                    \<Rightarrow> data \<Rightarrow> bool \<Rightarrow> obj_ref
                                    \<Rightarrow> obj_ref option
                                    \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "do_normal_transfer sender sbuf endpoint badge grant
                     receiver rbuf  \<equiv>
  do
    mi \<leftarrow> get_message_info sender;
    caps \<leftarrow> if grant then lookup_extra_caps sender sbuf mi <catch> K (return [])
      else return [];
    mrs_transferred \<leftarrow> copy_mrs sender sbuf receiver rbuf (mi_length mi);
    mi' \<leftarrow> transfer_caps mi caps endpoint receiver rbuf;
    set_message_info receiver $ MI mrs_transferred (mi_extra_caps mi')
                                   (mi_caps_unwrapped mi') (mi_label mi);
    as_user receiver $ set_register badge_register badge
  od"

text {* Transfer a message either involving a fault or not. *}
definition
  do_ipc_transfer :: "obj_ref \<Rightarrow> obj_ref option \<Rightarrow>
                       badge \<Rightarrow> bool \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_ipc_transfer sender ep badge grant
     receiver \<equiv> do

     recv_buffer \<leftarrow> lookup_ipc_buffer True receiver;
     fault \<leftarrow> thread_get tcb_fault sender;

     case fault
        of None \<Rightarrow> do
            send_buffer \<leftarrow> lookup_ipc_buffer False sender;
            do_normal_transfer sender send_buffer ep badge grant
                           receiver recv_buffer
            od
         | Some f \<Rightarrow> do_fault_transfer badge sender receiver recv_buffer
   od"

text {* Handle a message send operation performed on an endpoint by a thread.
If a receiver is waiting then transfer the message. If no receiver is available
and the thread is willing to block waiting to send then put it in the endpoint
sending queue. *}
definition
  send_ipc :: "bool \<Rightarrow> bool \<Rightarrow> badge \<Rightarrow> bool \<Rightarrow> bool
                \<Rightarrow> obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, det_ext) s_monad"
where
  "send_ipc block call badge can_grant can_donate thread epptr \<equiv> do
     ep \<leftarrow> get_endpoint epptr;
     case (ep, block) of
         (IdleEP, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_is_call = call \<rparr>);
               set_endpoint epptr $ SendEP [thread]
             od
       | (SendEP queue, True) \<Rightarrow> do
               set_thread_state thread (BlockedOnSend epptr
                                   \<lparr> sender_badge = badge,
                                     sender_can_grant = can_grant,
                                     sender_is_call = call\<rparr>);
               qs' \<leftarrow> sort_queue (queue @ [thread]);
               set_endpoint epptr $ SendEP qs'
             od
       | (IdleEP, False) \<Rightarrow> return ()
       | (SendEP queue, False) \<Rightarrow> return ()
       | (RecvEP (dest # queue), _) \<Rightarrow> do
                set_endpoint epptr $ (case queue of [] \<Rightarrow> IdleEP
                                                     | _ \<Rightarrow> RecvEP queue);
                recv_state \<leftarrow> get_thread_state dest;
                reply \<leftarrow> case recv_state
                  of (BlockedOnReceive _ reply) \<Rightarrow> do
                      do_ipc_transfer thread (Some epptr) badge can_grant dest;
                      maybeM reply_unlink_tcb reply;
                      return reply
                    od
                  | _ \<Rightarrow> fail;
                sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context dest;

                fault \<leftarrow> thread_get tcb_fault thread;
                if call \<or> fault \<noteq> None then
                  when (can_grant \<and> reply \<noteq> None) $ reply_push thread dest (the reply) can_donate
                else when (can_donate \<and> sc_opt = None) $ do
                   thread_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context thread;
                   sched_context_donate (the thread_sc) dest
                od;
                set_thread_state dest Running;
                possible_switch_to dest
              od
       | (RecvEP [], _) \<Rightarrow> fail
   od"

text {* Handle a message receive operation performed on an endpoint by a thread.
If a sender is waiting then transfer the message, otherwise put the thread in
the endpoint receiving queue. *}
definition
  isActive :: "notification \<Rightarrow> bool"
where
  "isActive ntfn \<equiv> case ntfn_obj ntfn
     of ActiveNtfn _ \<Rightarrow> True
      | _ \<Rightarrow> False"


text{* Helper function for performing \emph{signal} when receiving on a normal
endpoint *}
definition
  complete_signal :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "complete_signal ntfnptr tcb \<equiv> do
     ntfn \<leftarrow> get_notification ntfnptr;
     case ntfn_obj ntfn of
       ActiveNtfn badge \<Rightarrow> do
           as_user tcb $ set_register badge_register badge;
           set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn
         od
     | _ \<Rightarrow> fail
   od"

definition
  do_nbrecv_failed_transfer :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "do_nbrecv_failed_transfer thread = do as_user thread $ set_register badge_register 0; return () od"

definition
  receive_ipc :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> cap \<Rightarrow> unit det_ext_monad"
where
  "receive_ipc thread cap is_blocking reply_cap \<equiv> do
     (epptr,rights) \<leftarrow> (case cap
                       of EndpointCap ref badge rights \<Rightarrow> return (ref,rights)
                        | _ \<Rightarrow> fail);
     reply \<leftarrow> (case reply_cap of 
                 ReplyCap r \<Rightarrow> do
                   tptr \<leftarrow> get_reply_obj_ref reply_tcb r;
                   when (tptr \<noteq> None \<and> the tptr \<noteq> thread) $ cancel_ipc (the tptr);
                   return (Some r)
                 od 
               | NullCap \<Rightarrow> return None
               | _ \<Rightarrow> fail);
     ep \<leftarrow> get_endpoint epptr;
     ntfnptr \<leftarrow> get_tcb_obj_ref tcb_bound_notification thread;
     ntfn \<leftarrow> case_option (return default_notification) get_notification ntfnptr;
     if (ntfnptr \<noteq> None \<and> isActive ntfn)
     then
       complete_signal (the ntfnptr) thread
     else
       case ep
         of IdleEP \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr reply);
                  when (reply \<noteq> None) $
                    set_reply_obj_ref reply_tcb_update (the reply) (Some thread);
                  set_endpoint epptr (RecvEP [thread])
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
            | RecvEP queue \<Rightarrow> (case is_blocking of
              True \<Rightarrow> do
                  set_thread_state thread (BlockedOnReceive epptr reply);
                  when (reply \<noteq> None) $ set_reply_obj_ref reply_tcb_update (the reply) (Some thread);
                  (* schedule_tcb? *)
                  qs' \<leftarrow> sort_queue (queue @ [thread]);
                  set_endpoint epptr (RecvEP qs')
                od
              | False \<Rightarrow> do_nbrecv_failed_transfer thread)
          | SendEP q \<Rightarrow> do
              assert (q \<noteq> []);
              queue \<leftarrow> return $ tl q;
              sender \<leftarrow> return $ hd q;
              set_endpoint epptr $
                (case queue of [] \<Rightarrow> IdleEP | _ \<Rightarrow> SendEP queue);
              sender_state \<leftarrow> get_thread_state sender;
              data \<leftarrow> (case sender_state
                       of BlockedOnSend ref data \<Rightarrow> return data
                        | _ \<Rightarrow> fail);
              do_ipc_transfer sender (Some epptr)
                        (sender_badge data) (sender_can_grant data)
                        thread;
              fault \<leftarrow> thread_get tcb_fault sender;
              if sender_is_call data \<or> fault \<noteq> None
              then
                if sender_can_grant data \<and> reply \<noteq> None
                then do
                  sender_sc \<leftarrow> get_tcb_obj_ref tcb_sched_context sender;
                  donate \<leftarrow> return (sender_sc \<noteq> None);
                  reply_push sender thread (the reply) donate
                od
                else set_thread_state sender Inactive
              else do
                set_thread_state sender Running;
                possible_switch_to sender
              od
            od
   od"

section {* Asynchronous Message Transfers *}

text {* Helper function to handle a signal operation in the case
where a receiver is waiting. *}
definition
  update_waiting_ntfn :: "obj_ref \<Rightarrow> obj_ref list \<Rightarrow> obj_ref option \<Rightarrow> obj_ref option \<Rightarrow> badge \<Rightarrow>
                         (unit, 'z::state_ext) s_monad"
where
  "update_waiting_ntfn ntfnptr queue bound_tcb sc_ptr badge \<equiv> do
     assert (queue \<noteq> []);
     (dest,rest) \<leftarrow> return $ (hd queue, tl queue);
     set_notification ntfnptr $ \<lparr>
         ntfn_obj = (case rest of [] \<Rightarrow> IdleNtfn | _ \<Rightarrow> WaitingNtfn rest),
         ntfn_bound_tcb = bound_tcb,
         ntfn_sc = sc_ptr \<rparr>;
     maybe_donate_sc dest ntfnptr;
     set_thread_state dest Running;
     as_user dest $ set_register badge_register badge;
     do_extended_op (possible_switch_to dest)
   od"

text {* Handle a message send operation performed on a notification object.
If a receiver is waiting then transfer the message, otherwise combine the new
message with whatever message is currently waiting. *}

(* helper function for checking if thread is blocked *)
definition
  receive_blocked :: "thread_state \<Rightarrow> bool"
where
  "receive_blocked st \<equiv> case st of
       BlockedOnReceive _ _ \<Rightarrow> True
     | _ \<Rightarrow> False"

definition
  send_signal :: "obj_ref \<Rightarrow> badge \<Rightarrow> (unit, 'z::state_ext) s_monad"
where
  "send_signal ntfnptr badge \<equiv> do
    ntfn \<leftarrow> get_notification ntfnptr;
    case (ntfn_obj ntfn, ntfn_bound_tcb ntfn) of
          (IdleNtfn, Some tcb) \<Rightarrow> do
                  st \<leftarrow> get_thread_state tcb;
                  if (receive_blocked st)
                  then do
                      cancel_ipc tcb;
                      maybe_donate_sc tcb ntfnptr;
                      set_thread_state tcb Running;
                      as_user tcb $ set_register badge_register badge;
                      do_extended_op $ possible_switch_to tcb
                    od
                  else set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn badge)) ntfn
            od
       | (IdleNtfn, None) \<Rightarrow> set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn badge)) ntfn
       | (WaitingNtfn queue, bound_tcb) \<Rightarrow> update_waiting_ntfn ntfnptr queue bound_tcb (ntfn_sc ntfn) badge
       | (ActiveNtfn badge', _) \<Rightarrow>
           set_notification ntfnptr $ ntfn_obj_update (K (ActiveNtfn (combine_ntfn_badges badge badge'))) ntfn
   od"


text {* Handle a receive operation performed on a notification object by a
thread. If a message is waiting then perform the transfer, otherwise put the
thread in the endpoint's receiving queue. *}
definition
  receive_signal :: "obj_ref \<Rightarrow> cap \<Rightarrow> bool \<Rightarrow> unit det_ext_monad"
where
   "receive_signal thread cap is_blocking \<equiv> do
    ntfnptr \<leftarrow>
      case cap
        of NotificationCap ntfnptr badge rights \<Rightarrow> return ntfnptr
         | _ \<Rightarrow> fail;
    ntfn \<leftarrow> get_notification ntfnptr;
    case ntfn_obj ntfn
      of IdleNtfn \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          set_notification ntfnptr $ ntfn_obj_update (K (WaitingNtfn [thread])) ntfn;
                          maybe_return_sc ntfnptr thread;
                          schedule_tcb thread
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | WaitingNtfn queue \<Rightarrow>
                   (case is_blocking of
                     True \<Rightarrow> do
                          set_thread_state thread (BlockedOnNotification ntfnptr);
                          qs' \<leftarrow> sort_queue (queue @ [thread]);
                          set_notification ntfnptr $ ntfn_obj_update (K (WaitingNtfn qs')) ntfn;
                          maybe_return_sc ntfnptr thread;
                          schedule_tcb thread
                        od
                   | False \<Rightarrow> do_nbrecv_failed_transfer thread)
       | ActiveNtfn badge \<Rightarrow> do
                     as_user thread $ set_register badge_register badge;
                     set_notification ntfnptr $ ntfn_obj_update (K IdleNtfn) ntfn;
                     maybe_donate_sc thread ntfnptr
                   od
    od"

section {* Sending Fault Messages *}

text {* When a thread encounters a fault, retreive its fault handler capability
and send a fault message. *}
definition
  send_fault_ipc :: "obj_ref \<Rightarrow> cap \<Rightarrow> fault \<Rightarrow> bool \<Rightarrow> (bool, det_ext) f_monad"
where
  "send_fault_ipc tptr handler_cap fault can_donate \<equiv>
     (case handler_cap
       of EndpointCap ref badge rights \<Rightarrow>
           if AllowSend \<in> rights \<and> AllowGrant \<in> rights
           then liftE $ (do
               thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := Some fault \<rparr>) tptr;
               send_ipc True False (cap_ep_badge handler_cap)
                        True can_donate tptr (cap_ep_ptr handler_cap);
               return True
             od)
           else fail
        | NullCap \<Rightarrow> liftE $ return False
        | _ \<Rightarrow> fail)"

text {* timeout fault *}
definition handle_timeout :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit, det_ext) s_monad"
where
  "handle_timeout tptr ex \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb tptr;
     assert (is_ep_cap (tcb_timeout_handler tcb));
     send_fault_ipc tptr (tcb_timeout_handler tcb) ex False;
     return ()
  od"

text {* If a fault message cannot be sent then leave the thread inactive. *}
definition
  handle_no_fault :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "handle_no_fault tptr \<equiv> set_thread_state tptr Inactive"

text {* Handle a thread fault by sending a fault message if possible. *}
definition
  handle_fault :: "obj_ref \<Rightarrow> fault \<Rightarrow> (unit, det_ext) s_monad"
where
  "handle_fault thread ex \<equiv> do
     tcb \<leftarrow> gets_the $ get_tcb thread;
     has_fh \<leftarrow> send_fault_ipc thread (tcb_fault_handler tcb) ex True
                    <catch> K (return False);
     unless has_fh $ (handle_no_fault thread);
     return ()
   od"

text {* Transfer a reply message and delete the one-use Reply capability. *}
definition is_timeout_fault :: "fault \<Rightarrow> bool" where
  "is_timeout_fault f \<equiv>
    (case f of Timeout _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  do_reply_transfer :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> (unit, det_ext) s_monad"
where
 "do_reply_transfer sender reply \<equiv> do
    recv_opt \<leftarrow> get_reply_tcb reply;
    swp maybeM recv_opt (\<lambda>receiver. do
      state \<leftarrow> get_thread_state receiver;
      case state of BlockedOnReply r \<Rightarrow>
      if r =(Some reply) then do
        reply_remove reply;
        fault \<leftarrow> thread_get tcb_fault receiver;
        case fault of
          None \<Rightarrow> do
             do_ipc_transfer sender None 0 True receiver;
             set_thread_state receiver Running
          od
        | Some f \<Rightarrow> do
             mi \<leftarrow> get_message_info sender;
             buf \<leftarrow> lookup_ipc_buffer False sender;
             mrs \<leftarrow> get_mrs sender buf mi;
             restart \<leftarrow> handle_fault_reply f receiver (mi_label mi) mrs;
             thread_set (\<lambda>tcb. tcb \<lparr> tcb_fault := None \<rparr>) receiver;
             set_thread_state receiver (if restart then Restart else Inactive);

            sc_opt \<leftarrow> get_tcb_obj_ref tcb_sched_context receiver;
            state2 \<leftarrow> get_thread_state receiver;
            when (sc_opt \<noteq> None \<and> runnable state2) $ do
              sc_ptr \<leftarrow> assert_opt sc_opt;
              refill_unblock_check sc_ptr;
              sc \<leftarrow> get_sched_context sc_ptr;

              cur_time \<leftarrow> gets cur_time;
              ready \<leftarrow> return $ (r_time (refill_hd sc)) \<le> cur_time + kernelWCET_ticks; (* refill_ready sc_ptr *)

              sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills sc); (* refill_sufficient sc_ptr 0 *)

              if (ready \<and> sufficient) then possible_switch_to receiver
              else do
                tcb \<leftarrow> gets_the $ get_tcb receiver;
                if (is_ep_cap (tcb_timeout_handler tcb) \<and> \<not> is_timeout_fault f) then
                  handle_timeout receiver (Timeout (sc_badge sc))
                else postpone sc_ptr
              od
            od
         od
       od
       else fail
    | _ \<Rightarrow> return ()
    od)
  od"

text {* This function transfers a reply message to a thread when that message
is generated by a kernel service. *}
definition
  reply_from_kernel :: "obj_ref \<Rightarrow> (data \<times> data list) \<Rightarrow> (unit,'z::state_ext) s_monad"
where
 "reply_from_kernel thread x \<equiv> do
    (label, msg) \<leftarrow> return x;
    buf \<leftarrow> lookup_ipc_buffer True thread;
    as_user thread $ set_register badge_register 0;
    len \<leftarrow> set_mrs thread buf msg;
    set_message_info thread $ MI len 0 0 label
  od"


(* below are moved from Schedule_A, due to a dependency issue *)

definition
  end_timeslice :: "bool \<Rightarrow> (unit,det_ext) s_monad"
where
  "end_timeslice canTimeout = do
     ct \<leftarrow> gets cur_thread;
     it \<leftarrow> gets idle_thread;
     when (ct \<noteq> it) $ do
       sc_ptr \<leftarrow> gets cur_sc;
       csc \<leftarrow> get_sched_context sc_ptr;

       cur_time \<leftarrow> gets cur_time;
       ready \<leftarrow> return $ (r_time (refill_hd csc)) \<le> cur_time + kernelWCET_ticks; (* refill_ready sc_ptr *)

       sufficient \<leftarrow> return $ sufficient_refills 0 (sc_refills csc); (* refill_sufficient sc_ptr 0 *)

       tcb \<leftarrow> gets_the $ get_tcb ct;
       if canTimeout \<and> (is_ep_cap (tcb_timeout_handler tcb)) then
         handle_timeout ct (Timeout (sc_badge csc))
       else if ready \<and> sufficient then do
         cur \<leftarrow> gets cur_thread;
         tcb_sched_action tcb_sched_append cur
       od
       else
         postpone sc_ptr
    od
  od"

definition
  charge_budget :: "ticks \<Rightarrow> ticks \<Rightarrow> bool \<Rightarrow> (unit, det_ext) s_monad"
where
  "charge_budget capacity consumed canTimeout = do
    csc_ptr \<leftarrow> gets cur_sc;
    robin \<leftarrow> is_round_robin csc_ptr;
    if robin then do
      refills \<leftarrow> get_refills csc_ptr;
      let rfhd = hd refills; rftl = last refills; rf_body = butlast (tl refills) in
        set_refills csc_ptr
          (rfhd \<lparr> r_amount := r_amount rfhd + r_amount rftl \<rparr> # rf_body @ [rftl \<lparr> r_amount := 0 \<rparr>])
    od
    else refill_budget_check csc_ptr consumed capacity;
    update_sched_context csc_ptr (\<lambda>sc. sc\<lparr>sc_consumed := (sc_consumed sc) + consumed \<rparr>);
    modify $ consumed_time_update (K 0);
    ct \<leftarrow> gets cur_thread;
    st \<leftarrow> get_thread_state ct;
    when (runnable st) $ do
      end_timeslice canTimeout;
      reschedule_required;
      modify (\<lambda>s. s\<lparr>reprogram_timer := True\<rparr>)
    od
  od"

definition
  check_budget :: "bool det_ext_monad"
where
  "check_budget = do
     csc \<leftarrow> gets cur_sc;
     consumed \<leftarrow> gets consumed_time;
     sc \<leftarrow> get_sched_context csc;
     capacity \<leftarrow> refill_capacity csc consumed;

     full \<leftarrow> return (size (sc_refills sc) = sc_refill_max sc); (* = refill_full csc *)

     robin \<leftarrow> return (sc_period sc = 0); (* is_round_robin csc;*)

     if (capacity \<ge> MIN_BUDGET \<and> (robin \<or> \<not>full)) then do
       dom_exp \<leftarrow> gets is_cur_domain_expired;
       if dom_exp then do
         modify (\<lambda>s. s\<lparr> reprogram_timer := True \<rparr>);
         reschedule_required;
         return False
      od
      else return True
    od
    else do
      consumed \<leftarrow> gets consumed_time;
      charge_budget capacity consumed True;
      return False
    od
  od"

definition
  check_budget_restart :: "bool det_ext_monad"
where
  "check_budget_restart = do
     result \<leftarrow> check_budget;
    cur \<leftarrow> gets cur_thread;
    st \<leftarrow> get_thread_state cur;
    when (\<not>result \<and> runnable st) $ set_thread_state cur Restart;
    return result
  od"

text \<open> The Scheduling Control invocation configures the budget of a scheduling context. \<close>
definition
  invoke_sched_control_configure :: "sched_control_invocation \<Rightarrow> (unit, det_ext) se_monad"
where
  "invoke_sched_control_configure iv \<equiv>
  case iv of InvokeSchedControlConfigure sc_ptr budget period mrefills badge \<Rightarrow> liftE $ do
    sc \<leftarrow> get_sched_context sc_ptr;
    set_sched_context sc_ptr (sc\<lparr>sc_badge:= badge\<rparr>);
    (period,mrefills) \<leftarrow> return (if budget = period then (0,MIN_REFILLS) else (period,mrefills));
         (* true in the above means we have round robin *)
    when (sc_tcb sc \<noteq> None) $ do
      tcb_ptr \<leftarrow> assert_opt $ sc_tcb sc;
      tcb_release_remove tcb_ptr;
      tcb_sched_action tcb_sched_dequeue tcb_ptr;
      cur_sc \<leftarrow> gets cur_sc;
      when (cur_sc = sc_ptr) $ do
        result \<leftarrow> check_budget;
        when result $ commit_time
      od;
      st \<leftarrow> get_thread_state tcb_ptr;
      if 0 < sc_refill_max sc then do
        when (runnable st) $ refill_update sc_ptr period budget mrefills;
        sched_context_resume sc_ptr;
        ct \<leftarrow> gets cur_thread;
        if (tcb_ptr = ct) then reschedule_required
        else when (runnable st) $ possible_switch_to tcb_ptr
      od
      else
        refill_new sc_ptr mrefills budget period
    od
  od"



end
