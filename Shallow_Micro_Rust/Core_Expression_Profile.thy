(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Core_Expression_Profile
  imports Shallow_Computation.Core_Expression
begin

named_theorems micro_rust_simps

declare shallow_computation_simps[micro_rust_simps]

setup \<open>Sign.root_path #> Sign.add_path "Core_Expression"\<close>

abbreviation panic ::
    \<open>String.literal \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>panic msg \<equiv> abort (Panic msg)\<close>

abbreviation unimplemented ::
    \<open>String.literal \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>unimplemented nm \<equiv> abort (Unimplemented nm)\<close>

abbreviation (input) scoped ::
    \<open>('s, 'v, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
      ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
  where \<open>scoped e \<equiv> e\<close>

type_synonym ('s, 'a, 'b, 'c, 'r, 'abort, 'i, 'o) urust_binop3 =
  \<open>('s, 'a, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'b, 'r, 'abort, 'i, 'o) expression \<Rightarrow>
    ('s, 'c, 'r, 'abort, 'i, 'o) expression\<close>

type_synonym ('s, 'a, 'r, 'abort, 'i, 'o) urust_binop =
  \<open>('s, 'a, 'a, 'a, 'r, 'abort, 'i, 'o) Core_Expression.urust_binop3\<close>

type_synonym ('s, 'a, 'c, 'r, 'abort, 'i, 'o) urust_binop2 =
  \<open>('s, 'a, 'a, 'c, 'r, 'abort, 'i, 'o) Core_Expression.urust_binop3\<close>

setup \<open>Sign.local_path\<close>

end
