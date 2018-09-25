(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Thread Control Blocks"

theory TCB_H
imports
  NotificationDecls_H
  TCBDecls_H
  CNode_H
  VSpace_H
  FaultHandlerDecls_H
  SchedContext_H
  "./$L4V_ARCH/ArchTCB_H"
  "../../lib/HaskellLib_H"
begin

context begin interpretation Arch .
requalify_consts
  decodeTransfer
  gpRegisters
  frameRegisters
  getRegister
  setNextPC
  getRestartPC
  sanitiseRegister
  getSanitiseRegisterInfo
  setRegister
  performTransfer
  msgInfoRegister
  msgRegisters
  fromVPtr
  setTCBIPCBuffer
  postModifyRegisters
  max_us_to_ticks
end

abbreviation "mapMaybe \<equiv> option_map"

#INCLUDE_HASKELL SEL4/Object/TCB.lhs Arch= bodies_only NOT liftFnMaybe assertDerived archThreadGet archThreadSet asUser sanitiseRegister getSanitiseRegisterInfo takeWhileM sort_key

defs asUser_def:
"asUser tptr f\<equiv> (do
        uc \<leftarrow> threadGet  (atcbContextGet o tcbArch) tptr;
        (a, uc') \<leftarrow> select_f (f uc);
        threadSet (\<lambda> tcb. tcb \<lparr> tcbArch := atcbContextSet uc' (tcbArch tcb)\<rparr>) tptr;
        return a
od)"

end
