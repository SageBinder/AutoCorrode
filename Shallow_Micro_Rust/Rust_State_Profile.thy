(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Rust_State_Profile
  imports
    Shallow_State.State_References
    Shallow_State.Global_Store
    Core_Expression_Profile
begin
(*>*)

section\<open>Rust reference profile\<close>

definition mut_ref_from_ref ::
    \<open>('a, 'b, 'v) State_References.ref \<Rightarrow>
      ('a, 'b, 'v) State_References.ref\<close>
  where
  \<open>mut_ref_from_ref \<equiv> id\<close>

\<comment>\<open>This empty type class serves as an annotation for types which can appear as the global type
  of a lens. The main example are records, and the main non-example are references. In fact, the
  sole purpose of this class is to help disambiguate the overloaded \<^verbatim>\<open>.\<close>-operator in uRust in case
  the LHS is a reference. In this case, it is a priori not clear if we're focusing the LHS with respect
  to a lens between reference types, or with respect to the lifting of a lens on the value type of the ref.
  We always want the latter, and the \<^verbatim>\<open>localizable\<close> typeclass helps to enforce it.\<close>
class localizable
abbreviation (input) focus_lens_value :: \<open>('v::localizable, 'w) lens \<Rightarrow> 'v \<Rightarrow> 'w\<close> where
  \<open>focus_lens_value \<equiv> lens_view\<close>

consts
  focus_lens_const :: \<open>('v, 'w) lens \<Rightarrow> 'vp \<Rightarrow> 'wp\<close>

adhoc_overloading
  focus_lens_const \<rightleftharpoons> focus_reference_via_lens focus_lens_value

subsection\<open>Raw pointer casts\<close>

text\<open>Cast a raw (untyped) reference to a typed reference by attaching a prism-based focus.
This is the semantic content of Rust's @{verbatim \<open>ptr as *const T\<close>} and
@{verbatim \<open>ptr as *mut T\<close>} pointer casts. A raw
@{typ \<open>('addr, 'gv) State_References.gref\<close>} is promoted to a typed
@{typ \<open>('addr, 'gv, 'v) State_References.ref\<close>} via @{const make_focused}
with a prism-derived focus.

The @{text raw_ptr_cast_prism} constant is resolved via adhoc overloading to the appropriate
prism for the target type in each verification locale.\<close>

consts raw_ptr_cast_prism :: \<open>('gv, 'v) prism\<close>

definition raw_ptr_cast ::
  \<open>('gv, 'v) prism \<Rightarrow>
   ('s, ('addr, 'gv) State_References.gref, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, ('addr, 'gv, 'v) State_References.ref, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_ptr_cast p e \<equiv> bind e (\<lambda>gref. literal (make_focused gref (prism_to_focus p)))\<close>

abbreviation raw_ptr_cast_u8 ::
  \<open>('s, ('addr, 'gv) State_References.gref, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, ('addr, 'gv, 8 word) State_References.ref, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_ptr_cast_u8 \<equiv> raw_ptr_cast raw_ptr_cast_prism\<close>

abbreviation raw_ptr_cast_u16 ::
  \<open>('s, ('addr, 'gv) State_References.gref, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, ('addr, 'gv, 16 word) State_References.ref, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_ptr_cast_u16 \<equiv> raw_ptr_cast raw_ptr_cast_prism\<close>

abbreviation raw_ptr_cast_u32 ::
  \<open>('s, ('addr, 'gv) State_References.gref, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, ('addr, 'gv, 32 word) State_References.ref, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_ptr_cast_u32 \<equiv> raw_ptr_cast raw_ptr_cast_prism\<close>

abbreviation raw_ptr_cast_u64 ::
  \<open>('s, ('addr, 'gv) State_References.gref, 'c, 'abort, 'i, 'o) expression \<Rightarrow>
   ('s, ('addr, 'gv, 64 word) State_References.ref, 'c, 'abort, 'i, 'o) expression\<close> where
  \<open>raw_ptr_cast_u64 \<equiv> raw_ptr_cast raw_ptr_cast_prism\<close>

(*<*)
end
(*>*)
