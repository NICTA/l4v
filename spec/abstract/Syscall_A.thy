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
Top-level system call interface.
*)

chapter "System Calls"

theory Syscall_A
imports
  "../design/Event_H"
  Decode_A
  "./$L4V_ARCH/Init_A"
  "./$L4V_ARCH/Hypervisor_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_perform_invocation
  handle_vm_fault
  handle_hypervisor_fault
end


text{*
\label{c:syscall}

This theory defines the entry point to the kernel, @{term
call_kernel}, which is called by the assembly stubs after
switching into kernel mode and saving registers.
There are five kinds of events that end up in a switch to
kernel mode. These events are described by the enumerated type @{term
event}, defined in \autoref{sec:Event_H}. One of the five events is an
actual system call by the user, the other four are related to faults
and interrupts. There are seven different kinds of user system calls,
described by the enumerated type @{term syscall}, also defined in
\autoref{sec:Event_H}.

The @{text call_kernel} function delegates the event-specific behaviour
to @{text handle_event} which in turn further dispatches to system-call
specific handler functions.

In particular, two of the system calls, namely @{term SysSend} and
@{term SysCall}, correspond to a method invocation on capabilities.
They are handled in the @{term handle_invocation} operation, which is
made up of
three phases: first checking if the caller has the capabilities to
perform the operation, then decoding the arguments received from the
user (using the @{term decode_invocation} operation), and finally
actually performing the invocation (using the @{term
perform_invocation}).  These three phases are wrapped into a more
generic @{term syscall} framework function described below.
*}


section {* Generic system call structure\label{s:spec_syscall} *}


text{* The @{term syscall} operation generically describes the usual
execution of system calls in three phases, where the first phase may
result in a fault, the second phase may result in an error and the third
phase may be interrupted. The first two phases are used for argument decoding
and checking. The last phase commits and executes the system call.

The @{term syscall} operation has five arguments:
\begin{itemize}
\item the first operation @{text m_fault} to execute, that may
result in a fault;
\item the fault handler @{text h_fault} to execute if the first
operation resulted in a fault;
\item the second operation @{text m_error} to execute (if no fault
occurred in the first operation); this second operation may result in
an error;
\item the error handler @{text h_error} to execute if the second
operation resulted in an error;
\item the third and last operation @{text m_finalise} to execute (if
no error occurred in the second operation); this operation may be
interrupted.
\end{itemize}
*}

definition
  syscall :: "('a,'z::state_ext) f_monad
                  \<Rightarrow> (fault \<Rightarrow> ('c,'z::state_ext) s_monad)
                  \<Rightarrow> ('a \<Rightarrow> ('b,'z::state_ext) se_monad)
                  \<Rightarrow> (syscall_error \<Rightarrow> ('c,'z::state_ext) s_monad)
               \<Rightarrow> ('b \<Rightarrow> ('c,'z::state_ext) p_monad) \<Rightarrow> ('c,'z::state_ext) p_monad"
where
"syscall m_fault h_fault m_error h_error m_finalise \<equiv> doE
    r_fault \<leftarrow> without_preemption $ m_fault;
    case r_fault of
          Inl f \<Rightarrow>   without_preemption $ h_fault f
        | Inr a \<Rightarrow>   doE
            r_error \<leftarrow> without_preemption $ m_error a;
            case r_error of
                  Inl e \<Rightarrow>   without_preemption $ h_error e
                | Inr b \<Rightarrow>   m_finalise b
        odE
odE"


section {* System call entry point *}

text{* The kernel user can perform seven kinds of system calls,
described by the enumerated type @{term syscall}, defined in \autoref{s:spec_syscall}.
These seven system calls can be categorised into two broad
families: sending messages and receiving messages, the two main
services provided by the kernel.

The usual case for sending messages (@{text Send} event) consists of the user
sending a message to an object, without expecting any answer. The sender is
blocked until the receiver is waiting to receive. In case the
receiver is not trusted, an explicit non-blocking send operation can
be used (@{text NBSend} event). If a reply is requested from the
receiver, the Call operation can be used (@{text Call} event). The Call operation
will automatically provide a @{text Reply} capability to the receiver.

All three sending operations are handled by the @{text
handle_invocation} operation, which takes two boolean arguments, one
to indicate if a reply is requested and the other to indicate if the
send is blocking or not.

The other direction is the reception of messages. This is done by
performing a Recv operation on an endpoint kernel object. The receiver
is then blocked until a sender performs a Send operation on the
endpoint object, resulting in a message transfer between the sender
and the receiver. The receiver may also perform a Reply operation
(@{text Reply} event) in response to a @{text Call}, which is always
non-blocking. When the receiver is a user-level server, it generally
runs a loop waiting for messages. On handling a received message, the
server will send a reply and then return to waiting. To avoid
excessive switching between user and kernel mode, the kernel provides
a ReplyRecv operation, which is simply a Reply followed by Recv.

Finally, the last event, @{text Yield}, enables the user to donate its
remaining timeslice. *}

text{* The invocation is made up of three phases. The first phase
corresponds to a lookup of capabilities to check that the invocation
is valid. This phase can result in a fault if a given CSpace address
is invalid (see the function @{text "resolve_address_bits"}). The
second phase is the decoding of the arguments given by the user. This
is handled by the @{text decode_invocation} operation. This operation
can result in an error if, for example, the number of arguments is
less than required by the operation, or if some argument capability
has the wrong type. Finally, the actual invocation is performed, using
the @{text perform_invocation} function. Note that this last phase is
preemptable.
*}

fun
  perform_invocation :: "bool \<Rightarrow> bool \<Rightarrow> invocation \<Rightarrow> (data list,'z::state_ext) p_monad"
where
  "perform_invocation block call (InvokeUntyped i) =
    doE
      invoke_untyped i;
      returnOk []
    odE"

| "perform_invocation block call (InvokeEndpoint ep badge canGrant) =
    (without_preemption $ do
       thread \<leftarrow> gets cur_thread;
       send_ipc block call badge canGrant thread ep;
       return []
     od)"

| "perform_invocation block call (InvokeNotification ep badge) =
    doE
      without_preemption $ send_signal ep badge;
      returnOk []
    odE"

| "perform_invocation block call (InvokeTCB i) = invoke_tcb i"

| "perform_invocation block call (InvokeDomain tptr d) = invoke_domain tptr d"

| "perform_invocation block call (InvokeReply thread slot) =
    liftE (do
      sender \<leftarrow> gets cur_thread;
      do_reply_transfer sender thread slot;
      return []
    od)"

| "perform_invocation block call (InvokeCNode i) =
    doE
      invoke_cnode i;
      returnOk []
    odE"

| "perform_invocation block call (InvokeIRQControl i) =
   doE
     invoke_irq_control i;
     returnOk []
   odE"

| "perform_invocation block call (InvokeIRQHandler i) =
   doE
     liftE $ invoke_irq_handler i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeSchedContext i) =
   doE
     liftE $ invoke_sched_context i;
     returnOk []
   odE"

| "perform_invocation _ _ _ (InvokeSchedControl i) =
   doE
     liftE $ invoke_sched_control_configure i;
     returnOk []
   odE"

| "perform_invocation block call (InvokeArchObject i) =
    arch_perform_invocation i"


definition
  handle_invocation :: "bool \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "handle_invocation calling blocking \<equiv> doE
    thread \<leftarrow> liftE $ gets cur_thread;
    info \<leftarrow> without_preemption $ get_message_info thread;
    ptr \<leftarrow> without_preemption $ liftM data_to_cptr $
          as_user thread $ get_register cap_register;
    syscall
      (doE
         (cap, slot) \<leftarrow> cap_fault_on_failure (of_bl ptr) False $
                           lookup_cap_and_slot thread ptr;
         buffer \<leftarrow> liftE $ lookup_ipc_buffer False thread;
         extracaps \<leftarrow> lookup_extra_caps thread buffer info;
         returnOk (slot, cap, extracaps, buffer)
       odE)
      (\<lambda>fault. when blocking $ handle_fault thread fault)
      (\<lambda>(slot,cap,extracaps,buffer). doE
            args \<leftarrow> liftE $ get_mrs thread buffer info;
            decode_invocation (mi_label info) args ptr slot cap extracaps
       odE)
      (\<lambda>err. when calling $
            reply_from_kernel thread $ msg_from_syscall_error err)
      (\<lambda>oper. doE
            without_preemption $ set_thread_state thread Restart;
            reply \<leftarrow> perform_invocation blocking calling oper;
            without_preemption $ do
                state \<leftarrow> get_thread_state thread;
                case state of
                      Restart \<Rightarrow> do
                          when calling $
                              reply_from_kernel thread (0, reply);
                          set_thread_state thread Running
	                    od
                    | _ \<Rightarrow>  return ()
            od
       odE)
  odE"


definition
  handle_yield :: "(unit,'z::state_ext) s_monad" where
  "handle_yield \<equiv> do
     thread \<leftarrow> gets cur_thread;
     do_extended_op (tcb_sched_action (tcb_sched_dequeue) thread);
     do_extended_op (tcb_sched_action (tcb_sched_append) thread);
     do_extended_op (reschedule_required)
   od"

definition
  handle_send :: "bool \<Rightarrow> (unit,'z::state_ext) p_monad" where
  "handle_send bl \<equiv> handle_invocation False bl"

definition
  handle_call :: "(unit,'z::state_ext) p_monad" where
 "handle_call \<equiv> handle_invocation True True"

definition
  delete_caller_cap :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "delete_caller_cap t \<equiv> cap_delete_one (t, tcb_cnode_index 3)"

definition
  handle_recv :: "bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "handle_recv is_blocking \<equiv> do
     thread \<leftarrow> gets cur_thread;

     ep_cptr \<leftarrow> liftM data_to_cptr $ as_user thread $
                 get_register cap_register;

     (cap_fault_on_failure (of_bl ep_cptr) True $ doE
        ep_cap \<leftarrow> lookup_cap thread ep_cptr;

        let flt = (throwError $ MissingCapability 0)
        in
        case ep_cap
          of EndpointCap ref badge rights \<Rightarrow>
             (if AllowRecv \<in> rights
              then liftE $ do
                 delete_caller_cap thread;
                 receive_ipc thread ep_cap is_blocking
                od
              else flt)
           | NotificationCap ref badge rights \<Rightarrow> 
             (if AllowRecv \<in> rights
              then doE
                ntfn \<leftarrow> liftE $ get_notification ref;
                boundTCB \<leftarrow> returnOk $ ntfn_bound_tcb ntfn;
                if boundTCB = Some thread \<or> boundTCB = None
                then liftE $ receive_signal thread ep_cap is_blocking
                else flt
               odE
              else flt)
           | _ \<Rightarrow> flt
      odE)
      <catch> handle_fault thread
   od"

definition
  handle_reply :: "(unit,'z::state_ext) s_monad" where
 "handle_reply \<equiv> do
    thread \<leftarrow> gets cur_thread;
    caller_cap \<leftarrow> get_cap (thread, tcb_cnode_index 3);
    case caller_cap of
      ReplyCap caller False \<Rightarrow> do_reply_transfer thread caller (thread, tcb_cnode_index 3)
    | NullCap \<Rightarrow> return ()
    | _ \<Rightarrow> fail
  od"


section {* Top-level event handling  *}

fun
  handle_event :: "event \<Rightarrow> (unit, det_ext) p_monad"
where
  "handle_event (SyscallEvent call) = doE
    liftE $ update_time_stamp;
    restart \<leftarrow> liftE $ check_budget_restart;
    whenE restart (case call of
          SysSend \<Rightarrow> handle_send True
        | SysNBSend \<Rightarrow> handle_send False
        | SysCall \<Rightarrow> handle_call
        | SysRecv \<Rightarrow> without_preemption $ handle_recv True
        | SysYield \<Rightarrow> without_preemption handle_yield
        | SysReply \<Rightarrow> without_preemption handle_reply
        | SysReplyRecv \<Rightarrow> without_preemption $ do
            handle_reply;
            handle_recv True
          od
        | SysNBRecv \<Rightarrow> without_preemption $ handle_recv False)
  odE"

| "handle_event (UnknownSyscall n) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_fault thread $ UnknownSyscallException $ of_nat n
    od
  od)"

| "handle_event (UserLevelFault w1 w2) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_fault thread $ UserException w1 (w2 && mask 29)
    od
  od)"

| "handle_event Interrupt = (without_preemption $ do
    active \<leftarrow> do_machine_op getActiveIRQ;
    case active of
       Some irq \<Rightarrow> handle_interrupt irq
     | None \<Rightarrow> return ()
  od)"

| "handle_event (VMFaultEvent fault_type) = (without_preemption $ do
    update_time_stamp;
    restart \<leftarrow> check_budget_restart;
    when restart $ do
      thread \<leftarrow> gets cur_thread;
      handle_vm_fault thread fault_type <catch> handle_fault thread
    od
  od)"

| "handle_event (HypervisorEvent hypfault_type) = (without_preemption $ do
    thread \<leftarrow> gets cur_thread;
    handle_hypervisor_fault thread hypfault_type;
    return ()
  od)"


section {* Kernel entry point  *}

text {*
  This function is the main kernel entry point. The main event loop of the
  kernel handles events, handles a potential preemption interrupt, schedules
  and switches back to the active thread.
*}

definition
  call_kernel :: "event \<Rightarrow> (unit, det_ext) s_monad" where
  "call_kernel ev \<equiv> do
       handle_event ev <handle>
           (\<lambda>_. without_preemption $ do
                  irq \<leftarrow> do_machine_op getActiveIRQ;
                  when (irq \<noteq> None) $ do
                    commit \<leftarrow> check_budget;
                    when commit commit_time;
                    handle_interrupt (the irq)
                  od
                od);
       schedule;
       activate_thread
   od"

end
