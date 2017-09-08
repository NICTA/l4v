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
>          TCBSetIPCBuffer -> 8
>          TCBSetSpace -> 9
>          TCBSuspend -> 10
>          TCBResume -> 11
>          TCBBindNotification -> 12
>          TCBUnbindNotification -> 13
>          CNodeRevoke -> 14
>          CNodeDelete -> 15
>          CNodeCancelBadgedSends -> 16
>          CNodeCopy -> 17
>          CNodeMint -> 18
>          CNodeMove -> 19
>          CNodeMutate -> 20
>          CNodeRotate -> 21
>          IRQIssueIRQHandler -> 22
>          IRQAckIRQ -> 23
>          IRQSetIRQHandler -> 24
>          IRQClearIRQHandler -> 25
>          TCBSetSchedContext -> 26
>          SchedControlConfigure -> 27
>          SchedContextConsumed -> 28
>          SchedContextBind -> 29
>          SchedContextUnbind -> 30
>          SchedContextUnbindObject -> 31
>          DomainSetSet -> apiMax
>          ArchInvocationLabel a -> apiMax + 1 + fromEnum a
>          where apiMax = 32
>     toEnum n
>         | n == 0 = InvalidInvocation
>         | n == 1 = UntypedRetype
>         | n == 2 = TCBReadRegisters
>         | n == 3 = TCBWriteRegisters
>         | n == 4 = TCBCopyRegisters
>         | n == 5 = TCBConfigure
>         | n == 6 = TCBSetMCPriority
>         | n == 7 = TCBSetPriority
>         | n == 8 = TCBSetIPCBuffer
>         | n == 9 = TCBSetSpace
>         | n == 10 = TCBSuspend
>         | n == 11 = TCBResume
>         | n == 12 = TCBBindNotification
>         | n == 13 = TCBUnbindNotification
>         | n == 14 = CNodeRevoke
>         | n == 15 = CNodeDelete
>         | n == 16 = CNodeCancelBadgedSends
>         | n == 17 = CNodeCopy
>         | n == 18 = CNodeMint
>         | n == 19 = CNodeMove
>         | n == 20 = CNodeMutate
>         | n == 21 = CNodeRotate
>         | n == 22 = IRQIssueIRQHandler
>         | n == 23 = IRQAckIRQ
>         | n == 24 = IRQSetIRQHandler
>         | n == 25 = IRQClearIRQHandler
>         | n == 26 = TCBSetSchedContext
>         | n == 27 = SchedControlConfigure
>         | n == 28 = SchedContextConsumed
>         | n == 29 = SchedContextBind
>         | n == 30 = SchedContextUnbind
>         | n == 31 = SchedContextUnbindObject
>         | n == 32 = DomainSetSet
>         | n > apiMax = ArchInvocationLabel $ toEnum (n - 1 - apiMax)
>         | otherwise = error "toEnum out of range for InvocationLabel"
>         where apiMax = 32

Decode the invocation type requested by a particular message label.

> invocationType :: Word -> InvocationLabel
> invocationType x
>     | x' <= fromEnum (maxBound :: InvocationLabel) = toEnum x'
>     | otherwise = InvalidInvocation
>     where x' = fromIntegral x

