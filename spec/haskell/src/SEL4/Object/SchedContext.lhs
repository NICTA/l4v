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
>         setSchedContext, updateTimeStamp, commitTime, rollbackTime,
>         refillHd, minBudget, minBudgetUs, refillCapacity, refillBudgetCheck,
>         refillSplitCheck, isCurDomainExpired, refillUnblockCheck,
>         refillReadyTcb, refillReady, tcbReleaseEnqueue,
>         guardedSwitchTo, refillSufficient, postpone
>     ) where

\begin{impdetails}

> import SEL4.Machine.Hardware
> import SEL4.Machine.RegisterSet(PPtr)
> import SEL4.API.Failures(SyscallError(..))
> import SEL4.Model.Failures(KernelF, withoutFailure)
> import SEL4.Model.PSpace(getObject, setObject)
> import SEL4.Model.StateData
> import SEL4.Object.Structures
> import {-# SOURCE #-} SEL4.Object.TCB(threadGet, threadSet)
> import {-# SOURCE #-} SEL4.Kernel.Thread
> import SEL4.API.Invocation(SchedContextInvocation(..), SchedControlInvocation(..))

> import Data.Word(Word64)
> import Data.Maybe
> import qualified Data.Foldable as Foldable
> import Data.Set(fromList)

\end{impdetails}

> minBudget :: Word64
> minBudget = 2 * kernelWCETTicks

> minBudgetUs :: Word64
> minBudgetUs = 2 * kernelWCETUs

> getTcbSc :: PPtr TCB -> Kernel SchedContext
> getTcbSc tcbPtr = do
>     tcb <- getObject tcbPtr
>     scOpt <- return $ tcbSchedContext tcb
>     assert (scOpt /= Nothing) "SchedContext pointer must not be Nothing"
>     getSchedContext $ fromJust scOpt

> refillHd :: SchedContext -> Refill
> refillHd sc = head (scRefills sc)

> getScTime :: PPtr TCB -> Kernel Time
> getScTime tcbPtr = do
>     sc <- getTcbSc tcbPtr
>     return $ rTime (refillHd sc)

> tcbReleaseEnqueue :: PPtr TCB -> Kernel ()
> tcbReleaseEnqueue tcbPtr = do
>     time <- getScTime tcbPtr
>     qs <- getReleaseQueue
>     times <- mapM getScTime qs
>     qst <- return $ zip qs times
>     qst' <- return $ filter (\(_,t') -> t' <= time) qst ++ [(tcbPtr, time)] ++ filter (\(_,t') -> not (t' <= time)) qst
>     setReleaseQueue (map fst qst')

> refillsCapacity :: Time -> [Refill] -> Time
> refillsCapacity usage refills =
>     if rAmount (head refills) < usage
>         then 0
>         else rAmount (head refills) - usage

> sufficientRefills :: Time -> [Refill] -> Bool
> sufficientRefills usage refills = minBudget < refillsCapacity usage refills

> refillSufficient :: PPtr SchedContext -> Time -> Kernel Bool
> refillSufficient scPtr usage = do
>     refills <- getRefills scPtr
>     return $ sufficientRefills usage refills

> getRefills :: PPtr SchedContext -> Kernel [Refill]
> getRefills scPtr = do
>     sc <- getSchedContext scPtr
>     return $ scRefills sc

\subsection{Bind a TCB to a scheduling context}

> getSchedContext :: PPtr SchedContext -> Kernel SchedContext
> getSchedContext = getObject

> setSchedContext :: PPtr SchedContext -> SchedContext -> Kernel ()
> setSchedContext = setObject

> refillReady :: PPtr SchedContext -> Kernel Bool
> refillReady scPtr = do
>     curTime <- getCurTime
>     sc <- getSchedContext scPtr
>     scTime <- return $ rTime (refillHd sc)
>     return $ scTime <= curTime + kernelWCETTicks

> refillSize :: PPtr SchedContext -> Kernel Int
> refillSize scPtr = do
>     refills <- getRefills scPtr
>     return $ length refills

> refillSingle :: PPtr SchedContext -> Kernel Bool
> refillSingle scPtr = do
>     sz <- refillSize scPtr
>     return (sz == 1)

> refillsSum :: [Refill] -> Time
> refillsSum rf = Foldable.sum (fromList (map rAmount rf))

> refillSum :: PPtr SchedContext -> Kernel Time
> refillSum scPtr = do
>     refills <- getRefills scPtr
>     return $ refillsSum refills

> setRefills :: PPtr SchedContext -> [Refill] -> Kernel ()
> setRefills scPtr refills = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr (sc { scRefills = refills })

> refillPopHead :: PPtr SchedContext -> Kernel Refill
> refillPopHead scPtr = do
>     refills <- getRefills scPtr
>     assert (1 < length refills) "Length of Refill list must be greater than 1"
>     setRefills scPtr (tail refills)
>     return $ head refills

> refillAddTail :: PPtr SchedContext -> Refill -> Kernel ()
> refillAddTail scPtr rfl = do
>     assert (rAmount rfl /= 0) "rAmount of Refill must be non-zero"
>     sc <- getSchedContext scPtr
>     refills <- return $ scRefills sc
>     assert (length refills < scRefillMax sc) "Length of Refill list must be less than the maximum"
>     setRefills scPtr (refills ++ [rfl])

> refillNew :: PPtr SchedContext -> Int -> Ticks -> Ticks -> Kernel ()
> refillNew scPtr maxRefills budget period = do
>     sc <- getSchedContext scPtr
>     assert (minBudget < budget) "Budget must be greater than the minimum"
>     curTime <- getCurTime
>     refill <- return Refill { rTime = curTime, rAmount = budget }
>     sc' <- return $ sc { scPeriod = period, scRefills = [refill], scRefillMax = maxRefills }
>     setSchedContext scPtr sc'

> mergeRefill :: Refill -> Refill -> Refill
> mergeRefill r1 r2 =
>     Refill { rTime = rTime r1, rAmount = rAmount r2 + rAmount r1 }

> canMergeRefill r1 r2 = rTime r2 <= rTime r1 + rAmount r1

> refillsMergePrefix :: [Refill] -> [Refill]
> refillsMergePrefix [] = []
> refillsMergePrefix [r] = [r]
> refillsMergePrefix (r1 : r2 : rs) =
>     (if canMergeRefill r1 r2
>          then refillsMergePrefix (mergeRefill r1 r2 : rs)
>          else r1 : r2 : rs)

> refillUnblockCheck :: PPtr SchedContext -> Kernel ()
> refillUnblockCheck scPtr = do
>     ct <- getCurTime
>     refills <- getRefills scPtr
>     refills' <- return $ refillsMergePrefix ((head refills) { rTime = ct } : tail refills)
>     refills'' <- return
>         (if sufficientRefills 0 refills'
>              then refills'
>              else
>                  let
>                      r1 = head refills'
>                      r2 = head (tail refills')
>                      rs = tail (tail refills')
>                  in Refill { rTime = rTime r2, rAmount = rAmount r2 + rAmount r1 } : rs)
>     setRefills scPtr refills''

> refillsBudgetCheck :: Ticks -> Ticks -> [Refill] -> (Ticks, [Refill])
> refillsBudgetCheck _ usage [] = (usage, [])
> refillsBudgetCheck period usage (r:rs) =
>     (if rAmount r <= usage && 0 < rAmount r
>          then refillsBudgetCheck period (usage - rAmount r) (rs ++ [r { rTime = rTime r + period }])
>          else (usage, r:rs))

> refillBudgetCheck :: PPtr SchedContext -> Ticks -> Kernel Ticks
> refillBudgetCheck scPtr usage = do
>     sc <- getSchedContext scPtr
>     period <- return $ scPeriod sc
>     refills <- return $ scRefills sc

>     (usage', refills') <- return $ refillsBudgetCheck period usage refills

>     refills'' <- return
>         (if 0 < usage' && 0 < period
>          then
>              let r1 = head refills'
>                  r1' = r1 { rTime = rTime r1 + usage }
>                  rs = tail refills'
>              in if length rs > 0 && canMergeRefill r1' (head rs)
>                 then mergeRefill r1' (head rs) : tail rs
>                 else [r1]
>          else refills')

TODO: refills'' or refills'?

>     setRefills scPtr refills''
>     return usage'

> refillSplitCheck :: PPtr SchedContext -> Time -> Kernel ()
> refillSplitCheck scPtr usage = do
>     ct <- getCurTime
>     sc <- getSchedContext scPtr
>     refills <- return $ scRefills sc
>     rfhd <- return $ head refills
>     assert (0 < usage && usage <= rAmount rfhd) "Time usage must be within (0, rAmount)"
>     assert (rTime rfhd <= ct) "rTime must not be greater than the current time"

>     remaining <- return $ rAmount rfhd - usage
>     if remaining < minBudget && length refills == 1
>         then setRefills scPtr [Refill { rTime = rTime rfhd + scPeriod sc, rAmount = rAmount rfhd }]
>         else do
>             if length refills == scRefillMax sc || remaining < minBudget
>                 then
>                     let r2 = head (tail refills)
>                         rs = tail (tail refills)
>                     in setRefills scPtr (r2 { rAmount = rAmount r2 + remaining } : rs)
>                 else setRefills scPtr (rfhd { rAmount = remaining } : tail refills)
>             new <- return Refill { rTime = rTime rfhd + scPeriod sc, rAmount = usage }
>             refillAddTail scPtr new

> refillUpdate :: PPtr SchedContext -> Ticks -> Ticks -> Int -> Kernel ()
> refillUpdate scPtr newPeriod newBudget newMaxRefills =
>     refillNew scPtr newMaxRefills newBudget newPeriod

> postpone :: PPtr SchedContext -> Kernel ()
> postpone scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTcb sc
>     assert (tptrOpt /= Nothing) "postpone: scTcb must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     tcbSchedDequeue tptr
>     tcbReleaseEnqueue tptr
>     setReprogramTimer True

> schedContextResume :: Maybe (PPtr SchedContext) -> Kernel ()
> schedContextResume scPtrOpt = case scPtrOpt of 
>     Nothing -> return ()
>     Just scPtr -> do
>         sc <- getSchedContext scPtr
>         tptrOpt <- return $ scTcb sc
>         assert (tptrOpt /= Nothing) "schedContextResume: scTcb must not be Nothing"
>         tptr <- return $ fromJust tptrOpt
>         inRlsQueue <- inReleaseQueue tptr
>         sched <- isSchedulable tptr inRlsQueue
>         when sched $ do
>             refillUnblockCheck scPtr
>             ready <- refillReady scPtr
>             sufficient <- refillSufficient scPtr 0
>             runnable <- isRunnable tptr
>             when (runnable && 0 < scRefillMax sc && not (ready && sufficient)) $ postpone scPtr

> schedContextBind :: PPtr SchedContext -> PPtr TCB -> Kernel ()
> schedContextBind scPtr tcbPtr = do
>     sc <- getSchedContext scPtr
>     setSchedContext scPtr $ sc { scTcb = Just tcbPtr }
>     threadSet (\tcb -> tcb { tcbSchedContext = Just scPtr }) tcbPtr
>     schedContextResume (Just scPtr)

> schedContextUnbind :: PPtr SchedContext -> Kernel ()
> schedContextUnbind scPtr = do
>     sc <- getSchedContext scPtr
>     tptrOpt <- return $ scTcb sc
>     assert (tptrOpt /= Nothing) "schedContextUnbind: scTcb must not be Nothing"
>     tptr <- return $ fromJust tptrOpt
>     tcbSchedDequeue tptr
>     tcbReleaseRemove tptr
>     threadSet (\tcb -> tcb { tcbSchedContext = Nothing }) tptr
>     cur <- getCurThread
>     when (tptr == cur) $ rescheduleRequired

> schedContextUnbindAllTcbs :: PPtr SchedContext -> Kernel ()
> schedContextUnbindAllTcbs scPtr = do
>     sc <- getSchedContext scPtr
>     when (scTcb sc /= Nothing) $ schedContextUnbind scPtr

> unbindFromSc :: PPtr TCB -> Kernel ()
> unbindFromSc tcbPtr = do
>     scPtrOpt <- threadGet tcbSchedContext tcbPtr
>     when (scPtrOpt /= Nothing) $ schedContextUnbind (fromJust scPtrOpt)

> invokeSchedContext :: SchedContextInvocation -> KernelF SyscallError ()
> invokeSchedContext iv = withoutFailure $ case iv of
>     InvokeSchedContextBind scPtr tcbPtr -> schedContextBind scPtr tcbPtr
>     InvokeSchedContextUnbindObject scPtr -> schedContextUnbind scPtr
>     InvokeSchedContextUnbind scPtr -> schedContextUnbindAllTcbs scPtr

> invokeSchedControlConfigure :: SchedControlInvocation -> KernelF SyscallError ()
> invokeSchedControlConfigure iv = case iv of
>     InvokeSchedControlConfigure scPtr budget period mRefills -> withoutFailure $ do
>         sc <- getSchedContext scPtr
>         period <- return (if budget == period then 0 else period)
>         tptrOpt <- return $ scTcb sc
>         when (tptrOpt /= Nothing) $ do
>             assert (tptrOpt /= Nothing) "invokeSchedControlConfigure: scTcb must not be Nothing"
>             tptr <- return $ fromJust tptrOpt
>             tcbReleaseRemove tptr
>             runnable <- isRunnable tptr
>             if 0 < scRefillMax sc && runnable
>                 then do
>                     refillUpdate scPtr period budget mRefills
>                     schedContextResume (Just scPtr)
>                 else
>                     refillNew scPtr mRefills budget period

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

> commitTime :: Kernel ()
> commitTime = do
>     consumed <- getConsumedTime
>     ct <- getCurThread
>     it <- getIdleThread
>     when (0 < consumed && ct /= it) $ do
>         csc <- getCurSc
>         refillSplitCheck csc consumed
>     commitDomainTime
>     setConsumedTime 0

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

> refillCapacity :: PPtr SchedContext -> Time -> Kernel Time
> refillCapacity scPtr usage = do
>     refills <- getRefills scPtr
>     return $ refillsCapacity usage refills

> refillReadyTcb :: PPtr TCB -> Kernel Bool
> refillReadyTcb tptr = do
>     scOpt <- threadGet tcbSchedContext tptr
>     assert (scOpt /= Nothing) "refillReadyTcb: scOpt must not be Nothing"
>     scPtr <- return (fromJust scOpt)
>     refillReady scPtr

> guardedSwitchTo :: PPtr TCB -> Kernel ()
> guardedSwitchTo tptr = do
>     inq <- inReleaseQueue tptr
>     sched <- isSchedulable tptr inq
>     assert sched "guardedSwitchTo: thread must be schedulable"
>     switchToThread tptr

