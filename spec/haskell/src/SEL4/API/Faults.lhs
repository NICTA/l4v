%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module specifies the mechanisms used by the seL4 kernel to handle faults and exceptions generated by user-level code.

\begin{impdetails}

> {-# LANGUAGE CPP #-}

\end{impdetails}

> module SEL4.API.Faults where

\begin{impdetails}

> import SEL4.API.Types
> import SEL4.API.Failures
> import SEL4.Machine
> import SEL4.Model
> import SEL4.Object
> import SEL4.Object.SchedContext
> import SEL4.Object.Structures

\end{impdetails}

> import SEL4.API.Faults.TARGET

\subsection{Sending Fault IPC}

When a user-level task causes a fault or exception, represented in this model by the "Fault" type, the kernel performs a call to a user-level handler on the faulting thread's behalf. The following function defines the format and contents of the message that is sent by the kernel.

> makeFaultMessage :: Fault -> PPtr TCB -> Kernel (Word, [Word])
>
> makeFaultMessage (CapFault cptr rp lf) thread = do
>     pc <- asUser thread getRestartPC
>     return (1,
>         pc:fromCPtr cptr:fromIntegral (fromEnum rp):msgFromLookupFailure lf)

> makeFaultMessage (UnknownSyscallException n) thread = do
>     msg <- asUser thread $ mapM getRegister syscallMessage
>     return (2, msg ++ [n])

> makeFaultMessage (UserException exception code) thread = do
>     msg <- asUser thread $ mapM getRegister exceptionMessage
>     return (3, msg ++ [exception, code])

> makeFaultMessage (Timeout badge) thread = do
>     tcb <- getObject thread
>     scPtrOpt <- return $ tcbSchedContext tcb
>     case scPtrOpt of
>         Nothing -> return (5, [badge])
>         Just scPtr -> do
>             consumed <- schedContextUpdateConsumed scPtr
>             return (5, badge : setTimeArg consumed)

> makeFaultMessage (ArchFault af) thread = makeArchFaultMessage af thread

\subsection{Receiving Fault IPC Replies}

When the fault handler replies to a fault or exception call, the kernel modifies the state and execution context of the faulting thread. The new context and state depend on the type of fault and the contents of the fault handler's reply message.

For capability or VM faults, the reply is used only to restart the thread. For unknown system calls or other exceptions, this function expects to receive a message similar to that sent to the handler, which it will use to update the thread's register state. It will optionally restart the thread, depending on the label of the message.

This function returns "True" if the faulting thread should be restarted after the reply is received; otherwise it will remain suspended.

> handleFaultReply :: Fault -> PPtr TCB -> Word -> [Word] -> Kernel Bool
>
> handleFaultReply (CapFault {}) _ _ _ = return True
>
> handleFaultReply (UnknownSyscallException _) thread label msg = do
>     b <- getSanitiseRegisterInfo thread
>     asUser thread $ zipWithM_
>         (\r v -> setRegister r $ sanitiseRegister b r v)
>         syscallMessage msg
>     return (label == 0)

> handleFaultReply (UserException _ _) thread label msg = do
>     b <- getSanitiseRegisterInfo thread
>     asUser thread $ zipWithM_
>         (\r v -> setRegister r $ sanitiseRegister b r v)
>         exceptionMessage msg
>     return (label == 0)

> handleFaultReply (Timeout _) thread label msg = do
>     b <- getSanitiseRegisterInfo thread
>     asUser thread $ zipWithM_
>         (\r v -> setRegister r $ sanitiseRegister b r v)
>         timeoutMessage msg
>     return (label == 0)

> handleFaultReply (ArchFault af) thread label msg =
>     handleArchFaultReply af thread label msg

