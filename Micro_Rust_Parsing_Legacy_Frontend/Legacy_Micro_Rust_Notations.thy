(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Legacy_Micro_Rust_Notations
  imports
    Micro_Rust_Syntax
    Shallow_Micro_Rust_Base.Micro_Rust_Notations
begin

section\<open>Legacy notation grammar adapter\<close>

text\<open>
The production notation registry is syntax-neutral. This adapter supplies the
old frontend's bespoke productions for non-grammatical names. It replays
registrations already present when the legacy bundle is imported and observes
registrations made later in descendant theories.
\<close>

ML\<open>
structure Legacy_Micro_Rust_Notations =
struct
  structure Emitted = Theory_Data
  (
    type T = unit Symtab.table
    val empty = Symtab.empty
    val merge = Symtab.merge (K true)
  )

  fun is_grammatical_name name =
    let val remove_colons = String.translate (fn #":" => "" | c => String.str c)
    in
      Symbol_Pos.is_identifier name orelse
        Symbol_Pos.is_identifier (remove_colons name)
    end

  fun emit
      ({rust_name, hol_term, backend_const, ...} :
        Micro_Rust_Notation_Observers.registration) lthy =
    if is_grammatical_name rust_name orelse
       Symtab.defined (Emitted.get (Proof_Context.theory_of lthy)) rust_name
    then lthy
    else
      let
        val backend =
          (case backend_const of
             SOME name => name
           | NONE =>
               error (Pretty.string_of (Pretty.chunks
                 [Pretty.str ("micro_rust_notation: the uRust name " ^
                    quote rust_name ^
                    " needs a legacy bespoke grammar production"),
                  Pretty.str "whose markup binds to a single backend \
                    \constant, but the registered term has no constant head:",
                  Pretty.block
                    [Pretty.str "  ", Syntax.pretty_term lthy hol_term]])))
        val existing =
          maps (fn kind => Micro_Rust_Names.lookups lthy kind rust_name)
            [Micro_Rust_Names.NLiteral, Micro_Rust_Names.NFunction,
             Micro_Rust_Names.NField]
        val _ =
          if length existing <= 1 then ()
          else
            error ("micro_rust_notation: the non-grammatical name " ^
              quote rust_name ^ " cannot be overloaded by the legacy frontend")
        val sanitise =
          String.translate
            (fn character =>
              if Char.isAlphaNum character then String.str character else "")
        val syntax_constant =
          "_urust_identifier_bespoke_" ^ sanitise rust_name
        fun hook _ _ =
          Ast.Appl
            [Ast.Constant "_urust_identifier_id", Ast.Variable rust_name]
      in
        lthy
        |> Local_Theory.syntax_cmd true Syntax.mode_default
             [(syntax_constant, "urust_identifier",
               Mixfix.mixfix rust_name)]
        |> Local_Theory.background_theory
             (Sign.parse_ast_translation [(syntax_constant, hook)])
        |> Local_Theory.syntax_deps
             [(syntax_constant, [Lexicon.mark_const backend])]
        |> Local_Theory.background_theory
             (Emitted.map (Symtab.update (rust_name, ())))
      end

  fun replay_entry (kind, rust_name,
      {hol_term, reg_pos, backend_const, ...} : Micro_Rust_Names.entry) =
    emit
      {kind = kind,
       hol_src = "",
       rust_name = rust_name,
       rust_pos = reg_pos,
       hol_term = hol_term,
       backend_const = backend_const}

  fun install_and_replay lthy =
    let val registrations = Micro_Rust_Names.dump lthy
    in
      lthy
      |> Local_Theory.background_theory
           (Micro_Rust_Notation_Observers.register
             ("legacy-micro-rust-grammar", emit))
      |> fold replay_entry registrations
    end
end
\<close>

local_setup \<open>Legacy_Micro_Rust_Notations.install_and_replay\<close>

end
