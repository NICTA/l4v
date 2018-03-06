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
Functions for fault handling.
*)

chapter {* arch fault related functions *}

theory ArchFault_A
imports "../Structures_A" "../Tcb_A"
begin

context Arch begin global_naming ARM_A

fun make_arch_fault_msg :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> (data \<times> data list,'z::state_ext) s_monad"
where
 "make_arch_fault_msg (VMFault vptr archData) thread = do
     pc \<leftarrow> as_user thread getRestartPC;
     return (6, pc # vptr # archData) od"

definition
  handle_arch_fault_reply :: "arch_fault \<Rightarrow> obj_ref \<Rightarrow> data \<Rightarrow> data list \<Rightarrow> (bool,'z::state_ext) s_monad"
where
  "handle_arch_fault_reply vmf thread x y \<equiv> return True"


end

end