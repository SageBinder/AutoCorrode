(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature FRONTEND_DECLARATION_PLAN =
sig
  datatype declaration_kind =
      Constant
    | Type_Constructor
    | Fact
    | Other of string

  type declaration

  type term_obligation =
    {description: string,
     position: Position.T,
     term: term}

  type T
  type checked_declaration =
    {kind: declaration_kind,
     binding: binding,
     full_name: string,
     position: Position.T}
  type checked_plan

  val empty: T
  val declare:
    declaration_kind -> binding -> T -> T
  val declare_full:
    declaration_kind -> string -> Position.T -> T -> T
  val require_term:
    string -> Position.T -> term -> T -> T
  val declarations: T -> declaration list
  val term_obligations: T -> term_obligation list

  val preflight: local_theory -> T -> checked_plan
  val checked_declarations:
    checked_plan -> checked_declaration list
  val checked_terms: checked_plan -> term list
end

structure Frontend_Declaration_Plan : FRONTEND_DECLARATION_PLAN =
struct

datatype declaration_kind =
    Constant
  | Type_Constructor
  | Fact
  | Other of string

datatype declaration =
  Declaration of
    {kind: declaration_kind,
     binding: binding,
     full_name: string option,
     position: Position.T}

type term_obligation =
  {description: string,
   position: Position.T,
   term: term}

datatype T =
  Plan of
    {declarations: declaration list,
     term_obligations: term_obligation list}

type checked_declaration =
  {kind: declaration_kind,
   binding: binding,
   full_name: string,
   position: Position.T}

datatype checked_plan =
  Checked_Plan of
    {declarations: checked_declaration list,
     terms: term list}

val empty =
  Plan {declarations = [], term_obligations = []}

fun kind_name Constant = "constant"
  | kind_name Type_Constructor = "type constructor"
  | kind_name Fact = "fact"
  | kind_name (Other name) = name

fun kind_key Constant = "constant"
  | kind_key Type_Constructor = "type"
  | kind_key Fact = "fact"
  | kind_key (Other name) = "other:" ^ name

fun same_claim
    (Declaration
      {kind = left_kind, binding = left_binding,
       full_name = left_full_name, ...})
    (Declaration
      {kind = right_kind, binding = right_binding,
       full_name = right_full_name, ...}) =
  kind_key left_kind = kind_key right_kind andalso
  (case (left_full_name, right_full_name) of
     (SOME left, SOME right) => left = right
   | (NONE, NONE) =>
       Binding.long_name_of left_binding =
       Binding.long_name_of right_binding
   | _ => false)

fun declare kind binding
    (Plan {declarations, term_obligations}) =
  let
    val position = Binding.pos_of binding
    val _ =
      Frontend_Diagnostics.protect position
        ("invalid planned " ^ kind_name kind ^ " binding")
        (fn () => Binding.check binding)
    val declaration =
      Declaration
        {kind = kind, binding = binding,
         full_name = NONE, position = position}
    val _ =
      (case find_first (same_claim declaration) declarations of
         NONE => ()
       | SOME (Declaration {position = first_position, ...}) =>
           Frontend_Diagnostics.duplicate
             (kind_name kind)
             (Binding.long_name_of binding)
             first_position position)
  in
    Plan
      {declarations = declaration :: declarations,
       term_obligations = term_obligations}
  end

fun binding_of_full_name full_name =
  (case rev (Long_Name.explode full_name) of
     [] => Binding.empty
   | base :: reversed_qualifiers =>
       fold
         (Binding.qualify true)
         reversed_qualifiers
         (Binding.name base))

fun declare_full kind full_name position
    (Plan {declarations, term_obligations}) =
  let
    val _ =
      if full_name = "" then
        Frontend_Diagnostics.error_at position
          ("empty planned " ^ kind_name kind ^ " name")
      else ()
    val binding = binding_of_full_name full_name
    val declaration =
      Declaration
        {kind = kind, binding = binding,
         full_name = SOME full_name, position = position}
    val _ =
      (case find_first (same_claim declaration) declarations of
         NONE => ()
       | SOME (Declaration {position = first_position, ...}) =>
           Frontend_Diagnostics.duplicate
             (kind_name kind) full_name first_position position)
  in
    Plan
      {declarations = declaration :: declarations,
       term_obligations = term_obligations}
  end

fun require_term description position term
    (Plan {declarations, term_obligations}) =
  Plan
    {declarations = declarations,
     term_obligations =
       {description = description,
        position = position,
        term = term} :: term_obligations}

fun declarations (Plan {declarations, ...}) = rev declarations
fun term_obligations (Plan {term_obligations, ...}) =
  rev term_obligations

fun already_declared thy Constant name =
      Sign.declared_const thy name
  | already_declared thy Type_Constructor name =
      Sign.declared_tyname thy name
  | already_declared thy Fact name =
      Global_Theory.defined_fact thy name
  | already_declared _ (Other _) _ = false

fun check_declaration lthy
    (Declaration {kind, binding, full_name, position}) :
      checked_declaration =
  let
    val resolved_name =
      the_default (Local_Theory.full_name lthy binding) full_name
    val thy = Proof_Context.theory_of lthy
    val _ =
      if already_declared thy kind resolved_name
      then
        Frontend_Diagnostics.error_at position
          ("planned " ^ kind_name kind ^ " " ^ quote resolved_name ^
           " already exists")
      else ()
  in
    {kind = kind,
     binding = binding,
     full_name = resolved_name,
     position = position}
  end

fun check_resolved_duplicates declarations =
  let
    fun insert
        (declaration as {kind, full_name, position, ...}: checked_declaration)
        table =
      let
        val key = kind_key kind ^ "\000" ^ full_name
      in
        (case Symtab.lookup table key of
           NONE => Symtab.update (key, declaration) table
         | SOME {position = first_position, ...} =>
             Frontend_Diagnostics.duplicate
               (kind_name kind) full_name first_position position)
      end
  in
    fold insert declarations Symtab.empty
    |> K ()
  end

fun preflight lthy plan =
  let
    val checked_declarations =
      map (check_declaration lthy) (declarations plan)
    val _ = check_resolved_duplicates checked_declarations
    val checked_terms =
      term_obligations plan
      |> map
          (fn {description, position, term} =>
            Frontend_HOL_Term.check_term
              lthy position description term)
  in
    Checked_Plan
      {declarations = checked_declarations,
       terms = checked_terms}
  end

fun checked_declarations
    (Checked_Plan {declarations, ...}) = declarations
fun checked_terms (Checked_Plan {terms, ...}) = terms

end
