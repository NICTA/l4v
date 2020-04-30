(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchInterrupt_H
imports
  "../RetypeDecls_H"
  "../CNode_H"
  "../InterruptDecls_H"
  ArchInterruptDecls_H
  ArchHypervisor_H
begin

context Arch begin global_naming RISCV64_H

#INCLUDE_HASKELL SEL4/Object/Interrupt/RISCV64.hs CONTEXT RISCV64_H bodies_only ArchInv= Arch= NOT plic_complete_claim

end

end
