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
>         | TCBSetTimeoutEndpoint
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
>          TCBSetTimeoutEndpoint -> 9
>          TCBSetIPCBuffer -> 10
>          TCBSetSpace -> 11
>          TCBSuspend -> 12
>          TCBResume -> 13
>          TCBBindNotification -> 14
>          TCBUnbindNotification -> 15
>          CNodeRevoke -> 16
>          CNodeDelete -> 17
>          CNodeCancelBadgedSends -> 18
>          CNodeCopy -> 19
>          CNodeMint -> 20
>          CNodeMove -> 21
>          CNodeMutate -> 22
>          CNodeRotate -> 23
>          IRQIssueIRQHandler -> 24
>          IRQAckIRQ -> 25
>          IRQSetIRQHandler -> 26
>          IRQClearIRQHandler -> 27
>          TCBSetSchedContext -> 28
>          SchedControlConfigure -> 29
>          SchedContextConsumed -> 30
>          SchedContextBind -> 31
>          SchedContextUnbind -> 32
>          SchedContextUnbindObject -> 33
>          SchedContextYieldTo -> 34
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 35
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
>         | n == 9 = TCBSetTimeoutEndpoint
>         | n == 10 = TCBSetIPCBuffer
>         | n == 11 = TCBSetSpace
>         | n == 12 = TCBSuspend
>         | n == 13 = TCBResume
>         | n == 14 = TCBBindNotification
>         | n == 15 = TCBUnbindNotification
>         | n == 16 = CNodeRevoke
>         | n == 17 = CNodeDelete
>         | n == 18 = CNodeCancelBadgedSends
>         | n == 19 = CNodeCopy
>         | n == 20 = CNodeMint
>         | n == 21 = CNodeMove
>         | n == 22 = CNodeMutate
>         | n == 23 = CNodeRotate
>         | n == 24 = IRQIssueIRQHandler
>         | n == 25 = IRQAckIRQ
>         | n == 26 = IRQSetIRQHandler
>         | n == 27 = IRQClearIRQHandler
>         | n == 28 = TCBSetSchedContext
>         | n == 29 = SchedControlConfigure
>         | n == 30 = SchedContextConsumed
>         | n == 31 = SchedContextBind
>         | n == 32 = SchedContextUnbind
>         | n == 33 = SchedContextUnbindObject
>         | n == 34 = SchedContextYieldTo
>         | n == 35 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 35

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

