(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Corres
imports StateRelation "CorresK.CorresK_Lemmas"
begin

text \<open>Instantiating the corres framework to this particular state relation.\<close>
abbreviation
 "corres \<equiv> corres_underlying state_relation False True"

end
