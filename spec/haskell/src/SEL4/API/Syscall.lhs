%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module contains the top-level parts of the kernel model: the
system call interface, and the interrupt and fault handlers. It
exports the kernel entry points used by the simulator.

The system call interface is defined by functions in this module;
specifically by "handleEvent". This interface is distinct from the
interface to any specific type of kernel object; the operations that
may be performed on those objects are defined in their respective
modules.

> module SEL4.API.Syscall(Event(..), Syscall(..), handleEvent) where

\begin{impdetails}

> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.Kernel.Thread
> import SEL4.Kernel.CSpace
> import SEL4.Kernel.VSpace
> import SEL4.Kernel.FaultHandler
> import SEL4.Kernel.Hypervisor
> import SEL4.Object
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures
> import SEL4.Model
> import SEL4.Machine
> import Data.Bits

\end{impdetails}

\subsection{Types}

\subsubsection{Events}

The kernel model works by processing events caused by sources outside the kernel --- either user-level code or hardware devices. The following type defines the events that the kernel can respond to. Other than "Interrupt", they all include additional information about the nature of the event.

> data Event
>         = SyscallEvent Syscall
>         | UnknownSyscall Int
>         | UserLevelFault Word Word
>         | Interrupt
>         | VMFaultEvent VMFaultType
>         | HypervisorEvent HypFaultType
>         deriving Show

\subsubsection{System Calls}

The "SyscallEvent" constructor defined above requires an additional
value which specifies the system call that was made. This value is of
the enumerated type "Syscall":

> data Syscall
>         = SysCall
>         | SysReplyRecv
>         | SysNBSendRecv
>         | SysNBSendWait
>         | SysSend
>         | SysNBSend
>         | SysRecv
>         | SysYield
>         | SysNBRecv
>         | SysWait
>         | SysNBWait
>         deriving (Show, Enum, Bounded, Eq)

\subsection{Handling Events}

The "handleEvent" function determines the type of event, checks that
any user-supplied inputs are correct, and then calls internal kernel
functions to perform the appropriate actions. The parameter is the event being handled.

> handleEvent :: Event -> KernelP ()

\subsubsection{System Call Events}

System call events are dispatched here to the appropriate system call handlers, defined in the next section.

> handleEvent (SyscallEvent call) = do
>     withoutPreemption $ updateTimeStamp
>     restart <- withoutPreemption $ checkBudgetRestart
>     when restart (case call of
>         SysSend -> handleSend True
>         SysNBSend -> handleSend False
>         SysCall -> handleCall
>         SysRecv -> withoutPreemption $ handleRecv True True
>         SysYield -> withoutPreemption handleYield
>         SysReplyRecv -> withoutPreemption $ do
>             replyCptr <- getCapReg replyRegister
>             return $ handleInvocation False False True replyCptr
>             handleRecv True True
>         SysNBSendRecv -> do
>             dest <- withoutPreemption $ getCapReg nbsendRecvDest
>             handleInvocation False False True dest
>             withoutPreemption $ handleRecv True True
>         SysNBSendWait -> do
>             replyCptr <- withoutPreemption $ getCapReg replyRegister
>             handleInvocation False False True replyCptr
>             withoutPreemption $ handleRecv True False
>         SysWait -> withoutPreemption $ handleRecv True False
>         SysNBWait -> withoutPreemption $ handleRecv False False
>         SysNBRecv -> withoutPreemption $ handleRecv False True )

\subsubsection{Interrupts}

Interrupt handling is performed by "handleInterrupt", defined in \autoref{sec:object.interrupt.kernel.handling}.

> handleEvent Interrupt = withoutPreemption $ do
>     active <- doMachineOp (getActiveIRQ False)
>     case active of
>         Just irq -> handleInterrupt irq
>         Nothing -> doMachineOp $ debugPrint "spurious interrupt"

\subsubsection{Unknown System Calls}

An unknown system call raises an "UnknownSyscallException", which reports the system call number to the thread's fault handler. This may allow the fault handler to emulate system call interfaces other than seL4.

> handleEvent (UnknownSyscall n) = withoutPreemption $ do
>     updateTimeStamp
>     restart <- checkBudgetRestart
>     when restart $ do
>         thread <- getCurThread
>         handleFault thread $ UnknownSyscallException $ fromIntegral n

\subsubsection{Miscellaneous User-level Faults}

The "UserLevelFault" event represents a fault caused directly by user
level code. This might be, for example, an illegal instruction, or a
floating point exception. A real kernel implementation should provide
the handler with more information about the nature of the fault than
the following function does; the nature of that information is specific
to each architecture. In the second word, only the bottom 29 bits will
be communicated to the fault handler.

> handleEvent (UserLevelFault w1 w2) = withoutPreemption $ do
>     updateTimeStamp
>     restart <- checkBudgetRestart
>     when restart $ do
>         thread <- getCurThread
>         handleFault thread $ UserException w1 (w2 .&. mask 29)

\subsubsection{Virtual Memory Faults}

If the simulator reports a VM fault, the appropriate action depends on whether the architecture has a software-loaded TLB. If so, we look up the address, and then insert it into the TLB; otherwise we simply send a fault IPC.

> handleEvent (VMFaultEvent faultType) = withoutPreemption $ do
>     updateTimeStamp
>     restart <- checkBudgetRestart
>     when restart $ do
>         thread <- getCurThread
>         handleVMFault thread faultType `catchFailure` handleFault thread

\subsubsection{Hypervisor Faults}

For platforms running in hypervisor mode, many fault handlers are wrapped and redirected to standard fault handlers on kernel entry. Some however, such as VCPU faults on ARM plaftforms, require specialised handling.

> handleEvent (HypervisorEvent hypType) = withoutPreemption $ do
>     thread <- getCurThread
>     handleHypervisorFault thread hypType

\subsection{System Calls}

\subsubsection{Send System Call}

The "Send" system call sends a message to an object. The object is specified by a pointer to a capability in the caller's capability address space. The invocation is one-way; no reply is expected. This operation requires send rights on the invoked capability.

> handleSend :: Bool -> KernelP ()
> handleSend bl = do
>     cptr <- withoutPreemption $ getCapReg capRegister
>     handleInvocation False bl False cptr

\subsubsection{Call System Call}

The "Call" system call is similar to "Send", but it also requests a reply. For kernel capabilities, the kernel will provide information about the result of the operation directly. For synchronous endpoint capabilities, the receiver of the message will be provided with a single-use reply capability which it can use to send a reply and restart the caller. Notification and reply capabilities will immediately reply with a 0-length message.

> handleCall :: KernelP ()
> handleCall = do
>     cptr <- withoutPreemption $ getCapReg capRegister
>     handleInvocation True True True cptr

\subsubsection{Recv System Call}

The "Recv" system call blocks waiting to receive a message through a specified endpoint. It will fail if the specified capability does not refer to an endpoint object.

> handleRecv :: Bool -> Bool -> Kernel ()
> handleRecv isBlocking canReply = do
>     thread <- getCurThread
>     epCptr <- getCapReg capRegister
>     (do
>         epCap <- capFaultOnFailure epCptr True (lookupCap thread epCptr)
>         flt <- throw $ CapFault epCptr True (MissingCapability 0)
>         case epCap of
>             EndpointCap { capEPCanReceive = epCanReceive } -> do
>                 when (not epCanReceive) flt
>                 replyCap <- if canReply then lookupReply else return NullCap
>                 withoutFailure $ receiveIPC thread epCap isBlocking replyCap
>             NotificationCap { capNtfnCanReceive = True, capNtfnPtr = ntfnPtr } -> do
>                 ntfn <- withoutFailure $ getNotification ntfnPtr
>                 boundTCB <- return $ ntfnBoundTCB ntfn
>                 if boundTCB == Just thread || boundTCB == Nothing
>                     then withoutFailure $ receiveSignal thread epCap isBlocking
>                     else flt
>             _ -> flt) `catchFailure` handleFault thread

\subsubsection{Yield System Call}

The "Yield" system call is trivial; it simply moves the current thread to the end of its scheduler queue, then tells the scheduler to select a new thread.

> handleYield :: Kernel ()
> handleYield = do
>     curSc <- getCurSc
>     refills <- getRefills curSc
>     chargeBudget 0 (rAmount (head refills))

\subsection{Capability Invocations}\label{sel4:api:syscall:invoke}

The following function implements the "Send" and "Call" system calls. It determines the type of invocation, based on the object type; then it calls the appropriate internal kernel function to perform the operation.

> handleInvocation :: Bool -> Bool -> Bool -> CPtr -> KernelP ()
> handleInvocation isCall isBlocking canDonate cptr = do
>     thread <- withoutPreemption getCurThread
>     info <- withoutPreemption $ getMessageInfo thread
>     syscall

The destination capability's slot is located, and the capability read from it.

>         (do
>             (cap, slot) <- capFaultOnFailure cptr False $ lookupCapAndSlot thread cptr
>             buffer <- withoutFailure $ lookupIPCBuffer False thread
>             extracaps <- lookupExtraCaps thread buffer info
>             return (slot, cap, extracaps, buffer))

If a fault was encountered looking up the capability, and the invocation is a blocking one, a fault message is sent. If the invocation is non-blocking, the fault is ignored. In either case, no reply is sent.

>         (\fault ->
>             when isBlocking $ handleFault thread fault)

If there was no fault, then the capability, message registers and message label are used to determine the requested operation.

>         (\(slot, cap, extracaps, buffer) -> do
>             args <- withoutFailure $ getMRs thread buffer info
>             decodeInvocation (msgLabel info) args cptr slot cap extracaps)

If a system call error was encountered while decoding the operation, and the user is waiting for a reply, then generate an error message.

>         (\err -> when isCall $
>             replyFromKernel thread $ msgFromSyscallError err)

Otherwise, the operation is performed. If there is a result, it is converted to a success message (with label 0).

While the system call is running, the thread's state is set to "Restart", so any preemption will cause the system call to restart at user level when the thread resumes. If it is still set to "Restart" when the operation completes, it is reset to "Running" so the thread resumes at the next instruction. Also, if this is a call, then a reply message is generated when the thread is restarted.

>         (\oper -> do
>             withoutPreemption $ setThreadState Restart thread
>             reply <- performInvocation isBlocking isCall canDonate oper
>             withoutPreemption $ do
>                 state <- getThreadState thread
>                 case state of
>                     Restart -> do
>                         when isCall $ replyFromKernel thread (0, reply)
>                         setThreadState Running thread
>                     _ -> return ())

> getCapReg :: Register -> Kernel CPtr
> getCapReg reg = do
>     ct <- getCurThread
>     liftM CPtr $ asUser ct $ getRegister reg

> lookupReply :: KernelF Fault Capability
> lookupReply = do
>     cref <- withoutFailure $ getCapReg replyRegister
>     ct <- withoutFailure $ getCurThread
>     cap <- capFaultOnFailure cref True $ lookupCap ct cref
>     if isReplyCap cap
>         then return cap
>         else throw $ CapFault cref True (MissingCapability 0)

