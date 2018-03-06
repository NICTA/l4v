(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory KHeapPre_AI
imports "./$L4V_ARCH/Machine_AI"
begin

primrec
  same_caps :: "Structures_A.kernel_object \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
  "same_caps val (CNode sz cs)       = (val = CNode sz cs)"
| "same_caps val (TCB tcb)           = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
| "same_caps val (Endpoint ep)       = is_ep val"
| "same_caps val (Notification ntfn) = is_ntfn val"
| "same_caps val (SchedContext sc)   = is_sc val"
| "same_caps val (Reply r)           = is_reply val"
| "same_caps val (ArchObj ao)        = (\<exists>ao'. val = ArchObj ao')"


lemma same_caps_more_simps[simp]:
 "same_caps (CNode sz cs) val       = (val = CNode sz cs)"
 "same_caps (TCB tcb)     val       = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
 "same_caps (Endpoint ep) val       = is_ep val"
 "same_caps (Notification ntfn) val = is_ntfn val"
 "same_caps (SchedContext sc) val   = is_sc val"
 "same_caps (Reply r) val           = is_reply val"
 "same_caps (ArchObj ao) val        = (\<exists>ao'. val = ArchObj ao')"
 by (cases val, (fastforce simp: is_obj_defs)+)+

lemma dmo_return [simp]:
  "do_machine_op (return x) = return x"
  by (simp add: do_machine_op_def select_f_def return_def gets_def get_def
                bind_def modify_def put_def)

lemma get_object_sp:
  "\<lbrace>P\<rbrace> get_object p \<lbrace>\<lambda>r. P and ko_at r p\<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (auto simp add: obj_at_def)
  done

definition non_arch_obj :: "kernel_object \<Rightarrow> bool" where
  "non_arch_obj \<equiv> \<lambda>ko. \<forall>ako. ko \<noteq> ArchObj ako"

lemma non_arch_objs[intro]:
  "non_arch_obj (Endpoint ep)"
  "non_arch_obj (SchedContext sc)"
  "non_arch_obj (Reply reply)"
  "non_arch_obj (CNode sz cnode_contents)"
  "non_arch_obj (TCB tcb)"
  "non_arch_obj (Notification notification)"
  by (auto simp add: non_arch_obj_def)

definition arch_obj_pred :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> bool" where
  "arch_obj_pred P \<equiv>
    \<forall>ko ko'. non_arch_obj ko \<longrightarrow> non_arch_obj ko' \<longrightarrow>
      P ko = P ko'"

lemma arch_obj_predE:
  "\<lbrakk>arch_obj_pred P; non_arch_obj ko; non_arch_obj ko'\<rbrakk> \<Longrightarrow> P ko = P ko'"
  apply (unfold arch_obj_pred_def)
  apply (erule allE[where ?x="ko"])
  apply (erule allE[where ?x="ko'"])
  by blast

lemmas arch_obj_pred_defs = non_arch_obj_def arch_obj_pred_def

lemma arch_obj_pred_a_type[intro, simp]: "arch_obj_pred (\<lambda>ko. a_type ko = AArch T)"
  by (auto simp add: arch_obj_pred_defs a_type_def split: kernel_object.splits)

lemma
  arch_obj_pred_arch_obj_l[intro, simp]: "arch_obj_pred (\<lambda>ko. ArchObj ako = ko)" and
  arch_obj_pred_arch_obj_r[intro, simp]: "arch_obj_pred (\<lambda>ko. ko = ArchObj ako)"
  by (auto simp add: arch_obj_pred_defs)

lemma arch_obj_pred_fun_lift: "arch_obj_pred (\<lambda>ko. F (arch_obj_fun_lift P N ko))"
  by (simp add: arch_obj_pred_defs)

lemmas arch_obj_pred_fun_lift_id[simp]
  = arch_obj_pred_fun_lift[where F=id, simplified]

lemmas arch_obj_pred_fun_lift_k[intro]
  = arch_obj_pred_fun_lift[where F="K R" for R, simplified]

lemmas arch_obj_pred_fun_lift_el[simp]
  = arch_obj_pred_fun_lift[where F="\<lambda> S. x \<in> S" for x, simplified]

lemma arch_obj_pred_const_conjI[intro]:
  "arch_obj_pred P \<Longrightarrow>
    arch_obj_pred P' \<Longrightarrow>
    arch_obj_pred (\<lambda>ko. P ko \<and> P' ko)"
  apply (simp only: arch_obj_pred_def)
  apply blast
  done

lemma arch_obj_pred_fI:
  "(\<And>x. arch_obj_pred (P x)) \<Longrightarrow> arch_obj_pred (\<lambda>ko. f (\<lambda>x :: 'a :: type. P x ko))"
  apply (simp only: arch_obj_pred_def)
  apply (intro allI impI)
  apply (rule arg_cong[where f=f])
  by blast

declare
  arch_obj_pred_fI[where f=All, intro]
  arch_obj_pred_fI[where f=Ex, intro]

locale arch_only_obj_pred =
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes arch_only: "arch_obj_pred P"

lemma set_object_typ_at:
  "\<lbrace>\<lambda>s. typ_at (a_type ko) p s \<and> P (typ_at T p' s)\<rbrace>
  set_object p ko \<lbrace>\<lambda>rv s. P (typ_at T p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def)
  done

lemma set_object_neg_ko:
  "\<lbrace>not ko_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. \<not> ko_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: pred_neg_def obj_at_def)
  done

lemma get_tcb_SomeD: "get_tcb t s = Some v \<Longrightarrow> kheap s t = Some (TCB v)"
  apply (case_tac "kheap s t", simp_all add: get_tcb_def)
  apply (case_tac a, simp_all)
  done


lemma typ_at_same_type:
  assumes "typ_at T p s" "a_type k = a_type ko" "kheap s p' = Some ko"
  shows "typ_at T p (s\<lparr>kheap := kheap s(p' \<mapsto> k)\<rparr>)"
  using assms
  by (clarsimp simp: obj_at_def)


lemma hoare_to_pure_kheap_upd:
  assumes hoare[rule_format]:
    "\<And>f. (\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace>
      f \<lbrace>\<lambda>r s. P (typ_at (AArch T) p s)\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes typ_eq: "a_type k = a_type ko"
  assumes valid: "P (s :: ('z :: state_ext) state)"
  assumes at: "ko_at ko p s"
  shows "P (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (rule use_valid[where f="
      do
        s' <- get;
        assert (s' = s);
        (modify (\<lambda>s. s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>));
        return undefined
      od", OF _ hoare valid])
  apply (fastforce simp add: simpler_modify_def get_def bind_def
                             assert_def return_def[abs_def] fail_def)[1]
  apply wp
  apply (insert typ_eq at)
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  by (auto simp add: obj_at_def a_type_def split: kernel_object.splits if_splits)

lemma set_object_wp:
  "\<lbrace>\<lambda>s. Q (s\<lparr> kheap := kheap s (p \<mapsto> v)\<rparr>) \<rbrace> set_object p v \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  done

lemma get_object_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at ko p s \<longrightarrow> Q ko s\<rbrace> get_object p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
  done

end