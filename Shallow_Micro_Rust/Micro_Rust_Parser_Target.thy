(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Micro_Rust_Parser_Target
  imports
    Rust_Iterator
    Result_Type
    Numeric_Types
    Option_Type
    Range_Type
    Bool_Type
    Global_Store
    Prompts_And_Responses
    Tuple
    Micro_Rust_Notations
    "HOL-Library.Datatype_Records"
    Autogen.Autogen
    Lenses_And_Other_Optics.Lenses_And_Other_Optics
    Misc.Num_Case_Expression
  keywords
    "micro_rust_record" :: thy_decl
begin

section\<open>Semantic target vocabulary for Micro Rust parsers\<close>

text\<open>
This theory owns the semantic vocabulary used by Micro Rust parser
frontends. It contains no Micro Rust surface grammar, bracket quotation, or
parse translation.
\<close>

consts
  unwrap :: \<open>'a \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  expect :: \<open>'a \<Rightarrow> String.literal \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  store_update_const :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>
  store_reference_const :: \<open>'v \<Rightarrow> ('s, ('a, 'b, 'v) Global_Store.ref, 'abort, 'i, 'o) function_body\<close>
  store_dereference_const :: \<open>'a \<Rightarrow> ('s, 'v, 'abort, 'i, 'o) function_body\<close>
  index_const :: \<open>'a \<Rightarrow> 'idx \<Rightarrow> ('s, 'b, 'abort, 'i, 'o) function_body\<close>
  negation_const :: \<open>('s, 'v, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'v, 'c, 'abort, 'i, 'o) expression\<close>
  propagate_const :: \<open>('s, 'v, 'c, 'abort, 'i, 'o) expression \<Rightarrow> ('s, 'w, 'c, 'abort, 'i, 'o) expression\<close>
  assign_add_const :: \<open>('a, 'b, 'v) Global_Store.ref \<Rightarrow> 'w \<Rightarrow> ('s, unit, 'abort, 'i, 'o) function_body\<close>

adhoc_overloading propagate_const \<rightleftharpoons> propagate_option propagate_result
adhoc_overloading negation_const \<rightleftharpoons> negation Numeric_Types.word_bitwise_not
adhoc_overloading index_const \<rightleftharpoons>
  list_index array_index vector_index list_index_range array_index_range vector_index_range

section\<open>Canonical constructor names\<close>

setup \<open>
  fold Micro_Rust_Dispatch.register_backend_identity_wrapper
    [\<^const_name>\<open>lift_fun0\<close>,
     \<^const_name>\<open>lift_fun1\<close>,
     \<^const_name>\<open>lift_fun2\<close>,
     \<^const_name>\<open>lift_fun3\<close>,
     \<^const_name>\<open>lift_fun4\<close>,
     \<^const_name>\<open>lift_fun5\<close>,
     \<^const_name>\<open>lift_fun6\<close>,
     \<^const_name>\<open>lift_fun7\<close>,
     \<^const_name>\<open>lift_fun8\<close>,
     \<^const_name>\<open>lift_fun9\<close>,
     \<^const_name>\<open>lift_fun10\<close>,
     \<^const_name>\<open>lift_fun11\<close>,
     \<^const_name>\<open>lift_fun12\<close>,
     \<^const_name>\<open>lift_fun13\<close>,
     \<^const_name>\<open>lift_fun14\<close>]
\<close>

micro_rust_notation (call) \<open>lift_fun1 Some\<close> ("Some")
micro_rust_notation (call) \<open>lift_fun1 Ok\<close> ("Ok")
micro_rust_notation (call) \<open>lift_fun1 Err\<close> ("Err")

section\<open>Record support\<close>

named_theorems micro_rust_record_simps
named_theorems micro_rust_record_intros

ML\<open>
fun number_of_type_arguments ctxt (tyname : string) =
    tyname
 |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
 |> Term.dest_Type
 |> snd
 |> List.length

fun repeat (_ : 'a) 0 : 'a list = []
  | repeat (x : 'a) n : 'a list = x :: repeat x (n - 1)

fun generic_type_arguments ctxt tyname =
    tyname
 |> number_of_type_arguments ctxt
 |> repeat "type"

fun instantiate_localizable_class rec_name (ctxt : Proof.context) =
  let
    val typeargs = generic_type_arguments ctxt rec_name
    val full_tyname =
      rec_name
      |> Proof_Context.read_type_name {proper = true, strict = false} ctxt
      |> Term.dest_Type
      |> fst
  in
    ((Class.instance_arity_cmd ([full_tyname], typeargs, @{class localizable})
      #> Proof.global_default_proof
      #> Proof_Context.theory_of)
     |> Local_Theory.background_theory) ctxt
  end
\<close>

ML\<open>
fun register_lens_with_micro_rust rec_name overrides field lthy =
  let
    val name = lens_name rec_name field
    val full_name = Local_Theory.full_name lthy (Binding.name name)
    val (rust_name, rust_pos) =
      case AList.lookup (op =) overrides field of
        SOME name_and_pos => name_and_pos
      | NONE => (field, Position.thread_data ())
  in
    Micro_Rust_Notation_Cmd.do_register (SOME Micro_Rust_Names.NField)
      (full_name, (rust_name, rust_pos)) lthy
  end

fun check_override_fields rec_name fields overrides =
  let
    val unknown = filter_out (member (op =) fields) (map fst overrides)
  in
    if null unknown then ()
    else
      error ("micro_rust_record: unknown field(s) in uRust-name mapping: "
        ^ commas_quote unknown ^ "\nRecord " ^ quote rec_name
        ^ " has fields: " ^ commas_quote fields)
  end

fun register_lenses_with_micro_rust rec_name overrides thy =
  let val fields = get_fields rec_name thy
  in fold (register_lens_with_micro_rust rec_name overrides) fields thy end

fun summarise_micro_rust_record rec_name fields overrides with_fields =
  let
    fun urust_of field =
      case AList.lookup (op =) overrides field of
        SOME (rust_name, _) => rust_name
      | NONE => field
    fun field_facts field =
      let val base = rec_name ^ "_" ^ field
      in
        [base ^ "_lens", base ^ "_lens_view_update_modify", base ^ "_lens_valid",
         base ^ "_focus", base ^ "_focus_view_update_modify", base ^ "_focus_code",
         base ^ "_update_explicit", base ^ "_update_localI"]
      end
    fun render_field_map field =
      let val rust_name = urust_of field
      in if rust_name = field then field else rust_name ^ " \<mapsto> " ^ field end
    val urust_facts =
      if with_fields then map (fn field => "uRust field access: " ^ render_field_map field) fields
      else []
    val bullets = maps field_facts fields @ urust_facts @ [rec_name ^ " :: localizable"]
  in
    Pretty.writeln (Pretty.chunks (map (fn text => Pretty.str ("* " ^ text)) bullets))
  end

fun make_lenses ((with_fields, rec_name), overrides) _ lthy =
  let
    val _ =
      if with_fields orelse null overrides then ()
      else
        error "micro_rust_record: a uRust-name mapping cannot be combined \
          \with [no_fields], which suppresses field registration"
    val fields = get_fields rec_name lthy
    val _ = check_override_fields rec_name fields overrides
    val _ = summarise_micro_rust_record rec_name fields overrides with_fields
  in
    lthy
    |> lens_autogen_defs rec_name
    |> lens_autogen_defining_equations
         @{attributes [micro_rust_record_simps, focus_simps]} rec_name
    |> lens_autogen_prove_lens_validity
         @{attributes [micro_rust_record_intros, focus_intros,
                       micro_rust_record_simps, focus_simps]} rec_name
    |> lens_autogen_prove_update_equations
         @{attributes [micro_rust_record_simps, focus_simps]}
         @{attributes [micro_rust_record_intros, focus_intros]} rec_name
    |> focus_autogen_make_field_foci @{attributes [focus_components]} rec_name
    |> (if with_fields then register_lenses_with_micro_rust rec_name overrides else I)
    |> instantiate_localizable_class rec_name
  end

val parse_field_overrides =
  Scan.optional
    (Parse.$$$ "(" |--
      Parse.enum1 ","
        (Parse.short_ident -- (Parse.$$$ "=" |-- Parse.position Parse.string))
      --| Parse.$$$ ")")
    []

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>micro_rust_record\<close>
    "make lenses for datatype record"
    ((((Scan.optional ((Args.bracks (Args.$$$ "no_fields")) >> K false) true)
        -- Parse.short_ident)
      -- parse_field_overrides) >> make_lenses)
\<close>

end
