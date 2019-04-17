(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Accessing the RISCV64 VSpace"

theory ArchVSpaceAcc_A
imports "../KHeap_A"
begin

context Arch begin global_naming RISCV64_A

text \<open>
  This part of the specification is fairly concrete as the machine architecture is visible to
  the user in seL4 and therefore needs to be described. The abstraction compared to the
  implementation is in the data types for kernel objects. The interface which is rich in machine
  details remains the same.
\<close>

section "Encodings"

text \<open>The high bits of a virtual ASID.\<close>
definition asid_high_bits_of :: "asid \<Rightarrow> asid_high_index"
  where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"

text \<open>The low bits of a virtual ASID.\<close>
definition asid_low_bits_of :: "asid \<Rightarrow> asid_low_index"
  where
  "asid_low_bits_of asid \<equiv> ucast asid"

lemmas asid_bits_of_defs = asid_high_bits_of_def asid_low_bits_of_def

locale_abbrev
  "asid_table \<equiv> \<lambda>s. riscv_asid_table (arch_state s)"

section "Kernel Heap Accessors"

text \<open>Manipulate ASID pools, page directories and page tables in the kernel heap.\<close>

locale_abbrev aobjs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> arch_kernel_obj"
  where
  "aobjs_of \<equiv> \<lambda>s. kheap s |> aobj_of"

locale_abbrev asid_pools_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> asid_pool"
  where
  "asid_pools_of \<equiv> \<lambda>s. aobjs_of s |> asid_pool_of"

locale_abbrev get_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref, 'z::state_ext) s_monad"
  where
  "get_asid_pool \<equiv> gets_map asid_pools_of"

definition set_asid_pool :: "obj_ref \<Rightarrow> (asid_low_index \<rightharpoonup> obj_ref) \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "set_asid_pool ptr pool \<equiv> do
     get_asid_pool ptr;
     set_object ptr (ArchObj (ASIDPool pool))
   od"

locale_abbrev pts_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> pt"
  where
  "pts_of \<equiv> \<lambda>s. aobjs_of s |> pt_of"

locale_abbrev get_pt :: "obj_ref \<Rightarrow> (pt_index \<Rightarrow> pte,'z::state_ext) s_monad"
  where
  "get_pt \<equiv> gets_map pts_of"

definition set_pt :: "obj_ref \<Rightarrow> (pt_index \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "set_pt ptr pt \<equiv> do
     get_pt ptr;
     set_object ptr (ArchObj (PageTable pt))
   od"

(* The base address of the table a page table entry at p is in (assuming alignment) *)
locale_abbrev table_base :: "obj_ref \<Rightarrow> obj_ref" where
  "table_base p \<equiv> p && ~~mask pt_bits"

(* The index within the page table that a page table entry at p addresses *)
locale_abbrev table_index :: "obj_ref \<Rightarrow> pt_index" where
  "table_index p \<equiv> ucast (p && mask pt_bits >> pte_bits)"

(* p is the address of the pte,
   which consists of base (for the pt) and offset (for the index inside the pt).
   We assert that we avoid addresses between ptes. *)
definition pte_of :: "obj_ref \<Rightarrow> (obj_ref \<rightharpoonup> pt) \<rightharpoonup> pte"
  where
  "pte_of p \<equiv> do {
     oassert (is_aligned p pte_bits);
     pt \<leftarrow> oapply (table_base p);
     oreturn $ pt (table_index p)
   }"

locale_abbrev ptes_of :: "'z::state_ext state \<Rightarrow> obj_ref \<rightharpoonup> pte"
  where
  "ptes_of s \<equiv> \<lambda>p. pte_of p (pts_of s)"

text \<open>The following function takes a pointer to a PTE in kernel memory and returns the PTE.\<close>
locale_abbrev get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad"
  where
  "get_pte \<equiv> gets_map ptes_of"

definition store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "store_pte p pte \<equiv> do
     assert (is_aligned p pte_bits);
     base \<leftarrow> return $ table_base p;
     index \<leftarrow> return $ table_index p;
     pt \<leftarrow> get_pt (table_base p);
     pt' \<leftarrow> return $ pt (index := pte);
     set_pt base pt'
   od"


section "Basic Operations"

definition pt_bits_left :: "vm_level \<Rightarrow> nat"
  where
  "pt_bits_left level = ptTranslationBits * size level + pageBits"

definition pt_index :: "vm_level \<Rightarrow> vspace_ref \<Rightarrow> machine_word"
  where
  "pt_index level vptr \<equiv> (vptr >> pt_bits_left level) && mask ptTranslationBits"

text \<open>Interface function to extract the single top-level global page table:\<close>
definition riscv_global_pt :: "arch_state \<Rightarrow> obj_ref"
  where
  "riscv_global_pt s = the_elem (riscv_global_pts s max_pt_level)"

text \<open>
  The kernel window is mapped into every virtual address space from the @{term pptr_base}
  pointer upwards. This function copies the mappings which create the kernel window into a new
  top-level page table object.
\<close>
definition copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
  where
  "copy_global_mappings new_pm \<equiv> do
    global_pt \<leftarrow> gets (riscv_global_pt \<circ> arch_state);
    base \<leftarrow> return $ pt_index max_pt_level pptr_base;
    pt_size \<leftarrow> return $ 1 << ptTranslationBits;
    mapM_x (\<lambda>index. do
        offset \<leftarrow> return (index << pte_bits);
        pme \<leftarrow> get_pte (global_pt + offset);
        store_pte (new_pm + offset) pme
    od) [base  .e.  pt_size - 1]
  od"

text \<open>Walk page tables in software.\<close>

(* pte_addrs will always be at least page aligned *)
definition pptr_from_pte :: "pte \<Rightarrow> vspace_ref"
  where
  "pptr_from_pte pte \<equiv> ptrFromPAddr (pte_addr pte)"

definition pt_slot_offset :: "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref"
  where
  "pt_slot_offset level pt_ptr vptr = pt_ptr + (pt_index level vptr << pte_bits)"

definition pte_at_offset :: "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref \<rightharpoonup> pte) \<Rightarrow> pte option"
  where
  "pte_at_offset level pt_ptr vptr \<equiv> oapply (pt_slot_offset level pt_ptr vptr)"

text \<open>
  This is the base function for walking a page table structure.
  The walk proceeds from higher-level tables at the provided @{term level} (e.g. 2) to lower
  level tables, down to @{term bot_level} (e.g. 0). It returns a pointer to the page table where
  the walk stopped and the level of that table. The lookup stops when @{term bot_level} or a
  page is reached.
\<close>
fun pt_walk ::
  "vm_level \<Rightarrow> vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref \<rightharpoonup> pte) \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "pt_walk level bot_level pt_ptr vptr = do {
     if bot_level < level
     then do {
       pte \<leftarrow> oapply (pt_slot_offset level pt_ptr vptr);
       if is_PageTablePTE pte
         then pt_walk (level - 1) bot_level (pptr_from_pte pte) vptr
         else oreturn (level, pt_ptr)
     }
     else oreturn (level, pt_ptr)
   }"

declare pt_walk.simps[simp del]

text \<open>
  Looking up a slot in a page table structure. The function returns a level and an object
  pointer. The pointer is to a slot in a table at the returned level. If the returned level is 0,
  this slot is either an @{const InvalidPTE} or a @{const PagePTE}. If the returned level is higher
  the slot may also be a @{const PageTablePTE}.
\<close>
definition pt_lookup_slot_from_level ::
  "vm_level \<Rightarrow> vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref \<rightharpoonup> pte) \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "pt_lookup_slot_from_level level bot_level pt_ptr vptr = do {
     (level', pt_ptr') \<leftarrow> pt_walk level bot_level pt_ptr vptr;
     oreturn (level', pt_slot_offset level' pt_ptr' vptr)
   }"

definition pt_lookup_slot :: "obj_ref \<Rightarrow> vspace_ref \<Rightarrow> (obj_ref \<rightharpoonup> pte) \<Rightarrow> (vm_level \<times> obj_ref) option"
  where
  "pt_lookup_slot = pt_lookup_slot_from_level max_pt_level 0"

fun pt_lookup_from_level ::
  "vm_level \<Rightarrow> obj_ref \<Rightarrow> vspace_ref \<Rightarrow> obj_ref \<Rightarrow> (machine_word, 'z::state_ext) lf_monad"
  where
  "pt_lookup_from_level level pt_ptr vptr target_pt_ptr = doE
     unlessE (0 < level) $ throwError InvalidRoot;
     pte <- liftE $ gets_the $ pte_at_offset level pt_ptr vptr o ptes_of;
     unlessE (is_PageTablePTE pte) $ throwError InvalidRoot;
     ptr <- returnOk (pptr_from_pte pte);
     if ptr = target_pt_ptr
       then returnOk $ pt_slot_offset (level - 1) ptr vptr
       else pt_lookup_from_level (level - 1) ptr vptr target_pt_ptr
   odE"

declare pt_lookup_from_level.simps[simp del]

end
end
