%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module specifies the behavior of schedule context objects.

> module SEL4.Object.SchedContext (
>         schedContextUnbindAllTcbs, unbindFromSc, invokeSchedContext,
>         invokeSchedControlConfigure, getSchedContext,
>         schedContextUnbind, schedContextBind, schedContextResume,
>         setSchedContext, recharge, updateTimeStamp, commitTime,
>         isCurThreadExpired, rollbackTime
>     ) where

\begin{impdetails}

> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.API.Failures(SyscallError)
> import SEL4.Model.Failures(KernelF, withoutFailure)
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Model.StateData
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.Maybe

\end{impdetails}

\subsection{Bind a TCB to a scheduling context}

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> recharge :: PPtr SchedContext -> Kernel ()
> recharge scPtr = do
>     sc <- getSchedContext scPtr
>     assert (0 < scBudget sc) "recharge: scBudget should be greater than zero"
>     sc' <- return $ sc { scRemaining = scBudget sc }
>     setSchedContext scPtr sc'

TODO: Define tcbState ?? Global ?? runnable

> schedContextResume :: PPtr SchedContext -> Kernel ()
> schedContextResume scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTcb sc
>     runnable <- isRunnable tptr
>     when (runnable && 0 < scBudget sc) $ do
>         recharge scPtr
>         switchIfRequiredTo tptr

TODO: Define schedContextResume

> schedContextBind :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBind scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr $ sc { scTcb = Just tcbPtr }
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     schedContextResume scPtr

TODO: Define doExtendedOp, tcbSchedAction, tcbSchedDequeue, curThread, rescheduleRequired

> schedContextUnbind :: PPtr SchedContext -> Kernel ()
> schedContextUnbind scPtr = do
>     sc <- getSchedContext scPtr
>     tptr <- return $ fromJust $ scTcb sc
>     tcbSchedDequeue tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired

> schedContextUnbindAllTcbs :: PPtr SchedContext -> Kernel ()
> schedContextUnbindAllTcbs scPtr = do
>     sc <- getSchedContext scPtr
>     when (scTcb sc /= Nothing) $ schedContextUnbind scPtr

TODO: Define threadGet 

> unbindFromSc :: PPtr TCB -> Kernel ()
> unbindFromSc tcbPtr = do
>     scPtrOpt <- threadGet tcbSchedContext tcbPtr
>     when (scPtrOpt /= Nothing) $ schedContextUnbind (fromJust scPtrOpt)

TODO: Define schedContextInvocation

> invokeSchedContext :: SchedContextInvocation -> KernelF SyscallError ()
> invokeSchedContext iv = withoutFailure $ case iv of
>     InvokeSchedContextBind scPtr tcbPtr -> schedContextBind scPtr tcbPtr
>     InvokeSchedContextUnbindObject scPtr -> schedContextUnbind scPtr
>     InvokeSchedContextUnbind scPtr -> schedContextUnbindAllTcbs scPtr

TODO: Define schedControlInvocation, switchIfRequiredTo

> invokeSchedControlConfigure :: SchedControlInvocation -> KernelF SyscallError ()
> invokeSchedControlConfigure iv = case iv of
>     InvokeSchedControlConfigure scPtr budget -> withoutFailure $ do
>         sc <- getSchedContext scPtr
>         setSchedContext scPtr (sc { scBudget = budget })
>         recharge scPtr
>         when (scTcb sc /= Nothing) $ do
>             tcbPtr <- return $ fromJust (scTcb sc)
>             tcb <- threadGet id tcbPtr
>             scheduleTcb tcbPtr tcb
>             schedulable <- isSchedulable tcbPtr
>             if not schedulable
>                 then tcbSchedDequeue tcbPtr
>                 else switchIfRequiredTo tcbPtr

> isCurDomainExpired :: Kernel Bool
> isCurDomainExpired = do
>     domainTime <- getDomainTime
>     consumedTime <- getConsumedTime
>     return $! domainTime < consumedTime + kernelWCETTicks

> commitDomainTime :: Kernel ()
> commitDomainTime = do
>     domainTime <- getDomainTime
>     consumed <- getConsumedTime
>     time' <- return (if domainTime < consumed then 0 else domainTime - consumed)
>     setDomainTime time'

> commitTime :: PPtr SchedContext -> Kernel ()
> commitTime scPtr = do
>     sc <- getSchedContext scPtr
>     consumed <- getConsumedTime
>     rem' <- return $! (if scRemaining sc < consumed then 0 else scRemaining sc - consumed)
>     setSchedContext scPtr (sc{ scRemaining = rem' })
>     commitDomainTime
>     curTime <- getCurTime
>     setCurTime (curTime + consumed)
>     setConsumedTime 0

> isCurThreadExpired :: Kernel Bool
> isCurThreadExpired = do
>     cur <- getCurThread
>     tcb <- getObject cur
>     scPtr <- return $! (fromJust (tcbSchedContext tcb))
>     sc <- getSchedContext scPtr
>     consumed <- getConsumedTime
>     return $! (scRemaining sc < consumed + kernelWCETTicks)

> rollbackTime :: Kernel ()
> rollbackTime = do
>     consumed <- getConsumedTime
>     curTime <- getCurTime
>     setCurTime (curTime - consumed)
>     setConsumedTime 0

> updateTimeStamp :: Kernel ()
> updateTimeStamp = do
>     prevTime <- getCurTime
>     curTime' <- doMachineOp getCurrentTime
>     setCurTime curTime'
>     setConsumedTime (curTime' - prevTime)

