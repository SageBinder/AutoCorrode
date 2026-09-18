theory Parser_Utils
  imports "Parser_Common.Parser_Common"
begin

ML\<open>
structure Parser_Utils =
struct

type var_info = { free : term, def_pos : Position.T, id : int }

fun report_def kind ctxt id (x, def_pos) =
  (Context_Position.report ctxt def_pos Markup.bound;
   Context_Position.report ctxt def_pos
     (Position.make_entity_markup {def = true} id kind (x, def_pos)))

fun report_ref kind ctxt id (x, def_pos) use_pos =
  (Context_Position.report ctxt use_pos Markup.bound;
   Context_Position.report ctxt use_pos
     (Position.make_entity_markup {def = false} id kind (x, def_pos)))

fun bind_typed_var kind ctxt (env : var_info Symtab.table) ((x, def_pos), T) =
  let
    val id   = serial ()
    val _    = report_def kind ctxt id (x, def_pos)
    (* Source spelling belongs in the environment and markup, not in Free identity. Distinct
       identities prevent a later Term.lambda for a shadowing binder from capturing an outer
       same-spelled local that has been placed in a shared continuation. *)
    val free =
      Free ("_urust_local_" ^ string_of_int id ^ "_" ^ x, T)
  in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

fun bind_var kind ctxt env binding =
  bind_typed_var kind ctxt env (binding, dummyT)

(* Do not represent anonymous binders with invented Frees: such a name can capture a source binder held
   only in the elaboration environment. *)
fun anon_abs body = Abs (Name.uu, dummyT, body)

(* Parse lexical binders through fresh internal fixes, then restore their source Frees. Variants avoid
   collisions with same-named HOL context fixes while still shadowing constants during parsing. *)
fun parse_antiq kind ctxt env src =
  let
    val names = Symtab.keys env
    val (variants, ctxt') = Variable.variant_fixes names ctxt
    fun replacement source_name =
      (case Symtab.lookup env source_name of
         SOME {free, def_pos, id} =>
           {source_name = source_name, free = free, def_pos = def_pos, id = id}
       | NONE =>
           error ("internal missing antiquotation binder " ^ quote source_name))
    val replacements =
      Symtab.make
        (map2 (fn source_name => fn variant =>
          (variant, replacement source_name)) names variants)

    fun report_at {syntax, pos} markup =
      Context_Position.report ctxt pos
        (Markup.syntax_properties syntax markup)
    fun report_replacement
        {source_name, def_pos, id, ...} position =
      (report_at position Markup.bound;
       report_at position
         (Position.make_entity_markup {def = false} id kind
           (source_name, def_pos)))

    (* Syntax.parse_term has already decoded HOL binders to Abs/Bound and retained source positions as
       internal type constraints. Follow the same position flow as Isabelle's term decoder: constraints
       accumulate on one atom, while applications and abstractions start fresh occurrence scopes. *)
    fun restore positions
        ((constant as
            Const (\<^syntax_const>\<open>_type_constraint_\<close>,
              Type (\<^type_name>\<open>fun\<close>, [position_type, _]))) $ inner) =
          let
            val positions' =
              Term_Position.decode_positionT position_type @ positions
          in
            constant $ restore positions' inner
          end
      | restore _ (function $ argument) =
          restore [] function $ restore [] argument
      | restore _ (Abs (name, T, body)) =
          Abs (name, T, restore [] body)
      | restore positions (free as Free (name, _)) =
          (case Symtab.lookup replacements name of
             SOME (replacement as {free = lexical_free, ...}) =>
               (List.app (report_replacement replacement) positions;
                lexical_free)
           | NONE => free)
      | restore _ atom = atom
  in
    restore [] (Syntax.parse_term ctxt' (Syntax.implode_input src))
  end

end
\<close>

end
