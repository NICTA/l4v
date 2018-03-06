%
% Copyright 2014, General Dynamics C4 Systems
%
% This software may be distributed and modified according to the terms of
% the GNU General Public License version 2. Note that NO WARRANTY is provided.
% See "LICENSE_GPLv2.txt" for details.
%
% @TAG(GD_GPL)
%

This module defines the machine-independent invocation labels.

\begin{impdetails}

This module makes use of the GHC extension allowing data types with no constructors.

> {-# LANGUAGE EmptyDataDecls, CPP #-}

\end{impdetails}

> module SEL4.API.InvocationLabels where

\begin{impdetails}

> import SEL4.Machine
> import qualified SEL4.API.InvocationLabels.TARGET as ArchLabels

\end{impdetails}

\subsection{Invocation Labels}

The following type enumerates all the kinds of invocations that clients can request of the kernel. The derived Enum instance defines the message label that clients should use when requesting that service. These labels are enumerated globally to ensure that no objects share an invocation label. This is to avoid confusion: service requests to the wrong object will fail immediately rather than perform unexpected actions.

> data InvocationLabel
>         = InvalidInvocation
>         | UntypedRetype
>         | TCBReadRegisters
>         | TCBWriteRegisters
>         | TCBCopyRegisters
>         | TCBConfigure
>         | TCBSetPriority
>         | TCBSetMCPriority
>         | TCBSetSchedParams
>         | TCBSetIPCBuffer
>         | TCBSetSchedContext
>         | TCBSetSpace
>         | TCBSuspend
>         | TCBResume
>         | TCBBindNotification
>         | TCBUnbindNotification
>         | CNodeRevoke
>         | CNodeDelete
>         | CNodeCancelBadgedSends
>         | CNodeCopy
>         | CNodeMint
>         | CNodeMove
>         | CNodeMutate
>         | CNodeRotate
>         | IRQIssueIRQHandler
>         | IRQAckIRQ
>         | IRQSetIRQHandler
>         | IRQClearIRQHandler
>         | DomainSetSet
>         | SchedControlConfigure
>         | SchedContextConsumed
>         | SchedContextBind
>         | SchedContextUnbind
>         | SchedContextUnbindObject
>         | SchedContextYieldTo
>         | ArchInvocationLabel ArchLabels.ArchInvocationLabel
>         deriving (Show, Eq)

> instance Bounded InvocationLabel where
>     minBound = InvalidInvocation
>     maxBound = ArchInvocationLabel $ (maxBound :: ArchLabels.ArchInvocationLabel)

> instance Enum InvocationLabel where
>     fromEnum e = case e of
>          InvalidInvocation -> 0
>          UntypedRetype -> 1
>          TCBReadRegisters -> 2
>          TCBWriteRegisters -> 3
>          TCBCopyRegisters -> 4
>          TCBConfigure -> 5
>          TCBSetPriority -> 6
>          TCBSetMCPriority -> 7
>          TCBSetSchedParams -> 8
>          TCBSetIPCBuffer -> 9
>          TCBSetSpace -> 10
>          TCBSuspend -> 11
>          TCBResume -> 12
>          TCBBindNotification -> 13
>          TCBUnbindNotification -> 14
>          CNodeRevoke -> 15
>          CNodeDelete -> 16
>          CNodeCancelBadgedSends -> 17
>          CNodeCopy -> 18
>          CNodeMint -> 19
>          CNodeMove -> 20
>          CNodeMutate -> 21
>          CNodeRotate -> 22
>          IRQIssueIRQHandler -> 23
>          IRQAckIRQ -> 24
>          IRQSetIRQHandler -> 25
>          IRQClearIRQHandler -> 26
>          TCBSetSchedContext -> 27
>          SchedControlConfigure -> 28
>          SchedContextConsumed -> 29
>          SchedContextBind -> 30
>          SchedContextUnbind -> 31
>          SchedContextUnbindObject -> 32
>          SchedContextYieldTo -> 33
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 34
>     toEnum n
>         | n == 0 = InvalidInvocation
>         | n == 1 = UntypedRetype
>         | n == 2 = TCBReadRegisters
>         | n == 3 = TCBWriteRegisters
>         | n == 4 = TCBCopyRegisters
>         | n == 5 = TCBConfigure
>         | n == 6 = TCBSetMCPriority
>         | n == 7 = TCBSetPriority
>         | n == 8 = TCBSetSchedParams
>         | n == 9 = TCBSetIPCBuffer
>         | n == 10 = TCBSetSpace
>         | n == 11 = TCBSuspend
>         | n == 12 = TCBResume
>         | n == 13 = TCBBindNotification
>         | n == 14 = TCBUnbindNotification
>         | n == 15 = CNodeRevoke
>         | n == 16 = CNodeDelete
>         | n == 17 = CNodeCancelBadgedSends
>         | n == 18 = CNodeCopy
>         | n == 19 = CNodeMint
>         | n == 20 = CNodeMove
>         | n == 21 = CNodeMutate
>         | n == 22 = CNodeRotate
>         | n == 23 = IRQIssueIRQHandler
>         | n == 24 = IRQAckIRQ
>         | n == 25 = IRQSetIRQHandler
>         | n == 26 = IRQClearIRQHandler
>         | n == 27 = TCBSetSchedContext
>         | n == 28 = SchedControlConfigure
>         | n == 29 = SchedContextConsumed
>         | n == 30 = SchedContextBind
>         | n == 31 = SchedContextUnbind
>         | n == 32 = SchedContextUnbindObject
>         | n == 33 = SchedContextYieldTo
>         | n == 34 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 34

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

