theory Parser_Impl_Trait_Mappings
  imports Parser_Impl_Type_Mappings_Builtins
  keywords "urust_trait" :: thy_decl and "urust_consts"
begin

section\<open> Rust trait mappings \<close>

text\<open>
The command \<open>urust_trait "Path" = \<open>sort\<close>\<close> maps one Rust trait path to a HOL sort.
An optional \<open>urust_consts "NAME" = \<open>term\<close> and \<dots>\<close> clause supplies associated
constants, each represented by a polymorphic function from a type witness to a value whose type
does not depend on that witness. Mappings follow native context and locale scoping; interpreting a
locale transports their associated terms.

Lookups do not add reports. Resolving a source bound reports its trait declaration and its mapped
sort through the existing semantic-navigation transaction.
\<close>

ML\<open>
signature URUST_TRAIT_MAPPINGS =
sig
  datatype rust_trait_bound =
    Rust_Trait_Bound of (string * Position.T) list * URust_AST.source_layout
  type trait_entry =
    {path: string, pos: Position.T, sort: sort,
     constants: (string * {term: term, pos: Position.T}) list}

  val lookup: Proof.context -> string -> trait_entry option
  val resolve_bound: Proof.context -> rust_trait_bound -> trait_entry
  val associated_constant:
    Proof.context -> trait_entry -> string -> {term: term, pos: Position.T} option
  val traits_with_constant: Proof.context -> typ -> string -> (trait_entry * term) list
  val declare:
    {path: string * Position.T, sort: Input.source,
     constants: ((string * Position.T) * Input.source) list} ->
    local_theory -> local_theory
end

structure URust_Trait_Mappings :> URUST_TRAIT_MAPPINGS =
struct
  structure Navigation = Micro_Rust_Semantic_Navigation
  structure Reports = URust_Report_Transaction

  datatype rust_trait_bound =
    Rust_Trait_Bound of (string * Position.T) list * URust_AST.source_layout
  type trait_entry =
    {path: string, pos: Position.T, sort: sort,
     constants: (string * {term: term, pos: Position.T}) list}
  type registered = {entry: trait_entry, identity: serial}

  val traitN = "urust_trait"

  fun source_position source = Position.range_position (#2 (Input.source_content_range source))

  fun fail message pos = error ("urust_trait: " ^ message ^ Position.here pos)

  fun positioned pos action =
    (case Exn.result action () of
       Exn.Res value => value
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else fail (Runtime.exn_message exn) pos)

  fun identifier name =
    (case Symbol.explode name of
       first :: rest =>
         (Symbol.is_ascii_letter first orelse first = "_") andalso
         forall (fn symbol => Symbol.is_ascii_letter symbol orelse
           Symbol.is_ascii_digit symbol orelse symbol = "_") rest
     | [] => false)

  fun check_path (path, pos) =
    if forall identifier (URust_Import_Scope.key_segments path)
    then ()
    else fail ("malformed Rust trait path " ^ quote path) pos

  fun same_entry (left: trait_entry, right: trait_entry) =
    #sort left = #sort right andalso
    eq_list
      (fn ((name, {term, ...}), (name', {term = term', ...})) =>
        name = name' andalso term aconv term')
      (sort_by fst (#constants left), sort_by fst (#constants right))

  fun ordered (left: registered, right: registered) =
    if #identity left <= #identity right then (left, right) else (right, left)

  fun join path (left: registered, right: registered) =
    if same_entry (#entry left, #entry right) then #1 (ordered (left, right))
    else
      let val (first, second) = ordered (left, right) in
        error ("urust_trait: conflicting mappings for " ^ quote path ^
          Position.here_list [#pos (#entry first), #pos (#entry second)])
      end

  structure Data = Generic_Data
  (
    type T = registered Symtab.table
    val empty = Symtab.empty
    fun merge tables = Symtab.join join tables
  )

  fun table ctxt = Data.get (Context.Proof ctxt)
  fun lookup ctxt path = Option.map #entry (Symtab.lookup (table ctxt) path)

  fun add path candidate = Data.map (fn entries =>
    (case Symtab.lookup entries path of
       NONE => Symtab.update (path, candidate) entries
     | SOME active => Symtab.update (path, join path (active, candidate)) entries))

  fun morph phi ({entry = {path, pos, sort, constants}, identity}: registered) =
    {entry = {path = path, pos = pos, sort = sort,
      constants = map (apsnd (fn {term, pos} =>
        {term = Morphism.term phi term, pos = pos})) constants},
     identity = identity}: registered

  fun associated_constant _ (entry: trait_entry) name =
    AList.lookup (op =) (#constants entry) name

  fun domain term =
    (case fastype_of term of
       Type (\<^type_name>\<open>fun\<close>, [Type (\<^type_name>\<open>itself\<close>, [T]), result]) =>
         SOME (T, result)
     | _ => NONE)

  fun instantiate ctxt T term =
    let val (parameter, _) = the (domain term) in
      Term.map_types (Term.typ_subst_atomic [(parameter, T)]) term $
        Logic.mk_type T
      |> Proof_Context.cert_term ctxt
    end

  fun traits_with_constant ctxt T name =
    Symtab.dest (table ctxt)
    |> map_filter (fn (_, {entry, ...}) =>
      if Sign.of_sort (Proof_Context.theory_of ctxt) (T, #sort entry) then
        Option.map (fn {term, ...} => (entry, instantiate ctxt T term))
          (associated_constant ctxt entry name)
      else NONE)

  fun tooltip ctxt (entry: trait_entry) =
    #path entry ^ " = " ^ Syntax.string_of_sort ctxt (#sort entry)

  fun resolve_bound ctxt (Rust_Trait_Bound (segments, layout)) =
    let
      val path = space_implode "::" (map fst segments)
      val pos = (case rev segments of (_, pos) :: _ => pos | [] => URust_AST.source_span layout)
      val {entry, identity} =
        (case Symtab.lookup (table ctxt) path of
           SOME registered => registered
         | NONE => fail ("unregistered Rust trait " ^ quote path) pos)
      val _ = List.app (fn (_, position) =>
        Navigation.defer_report_text ctxt position Markup.typing (tooltip ctxt entry)) segments
      val _ = Navigation.defer_report ctxt pos
        (Position.make_entity_markup {def = false} identity traitN (path, #pos entry))
    in entry end

  fun checked_constant ctxt trait_sort ((name, name_pos), source) =
    let
      val pos = source_position source
      val _ = if identifier name then ()
        else fail ("malformed associated constant name " ^ quote name) name_pos
      val term = positioned pos (fn () => Reports.native ctxt
        (fn read_ctxt => Syntax.read_term read_ctxt (Syntax.implode_input source)))
      val (parameter, result) =
        (case domain term of
           SOME (parameter as TFree _, result) => (parameter, result)
         | SOME (parameter as TVar _, result) => (parameter, result)
         | _ => fail ("associated constant " ^ quote name ^
             " must have type 'a itself \<Rightarrow> result") pos)
      val _ =
        if Term.exists_subtype (fn T => T = parameter) result then
          fail ("associated constant " ^ quote name ^
            " result type depends on its witness type") pos
        else ()
      val _ =
        (case parameter of
           TFree (name, _) =>
             if is_some (Variable.def_sort ctxt (name, ~1)) then
               fail "associated constant witness type is fixed by the context" pos
             else ()
         | _ => ())
      val fresh = TFree (#1 (Name.variant "urust_trait_probe" (Variable.names_of ctxt)), trait_sort)
      (* Term certification checks raw constant instances; class requirements need a sort check. *)
      val _ =
        if Sign.of_sort (Proof_Context.theory_of ctxt) (fresh, Type.sort_of_atyp parameter) then ()
        else fail ("associated constant " ^ quote name ^ " requires sort " ^
          Syntax.string_of_sort ctxt (Type.sort_of_atyp parameter) ^
          " beyond mapped sort " ^ Syntax.string_of_sort ctxt trait_sort) pos
      val _ = positioned pos (fn () =>
        Proof_Context.cert_term ctxt
          (Term.map_types (Term.typ_subst_atomic [(parameter, fresh)]) term $
            Logic.mk_type fresh))
      val canonical = TVar (("_urust_trait", Term.maxidx_of_term term + 1), trait_sort)
      val normalized =
        Term.map_types (Term.typ_subst_atomic [(parameter, canonical)]) term
        |> Term_Subst.zero_var_indexes
    in (name, {term = normalized, pos = pos}) end

  fun prepare {path = path as (name, pos), sort = sort_source, constants} ctxt =
    let
      val _ = check_path path
      val sort = positioned (source_position sort_source) (fn () =>
        Reports.native ctxt (fn read_ctxt =>
          Syntax.read_sort read_ctxt (Syntax.implode_input sort_source))
        |> Sign.minimize_sort (Proof_Context.theory_of ctxt))
      val _ = fold (fn ((constant, position), _) => fn seen =>
        if member (op =) seen constant then
          fail ("duplicate associated constant " ^ quote constant) position
        else constant :: seen) constants []
      val checked = map (checked_constant ctxt sort) constants
    in
      {entry = {path = name, pos = pos, sort = sort, constants = checked},
       identity = serial ()}: registered
    end

  fun declare payload lthy =
    let
      val (completed, reports) = Reports.capture (fn () =>
        let
          val candidate as {entry, identity} = prepare payload lthy
          val path = #path entry
          val active = Symtab.lookup (table lthy) path
          val _ = Option.app (fn existing => ignore (join path (existing, candidate))) active
        in
          (case active of
             SOME _ => lthy
           | NONE =>
               let
                 val installed =
                   Local_Theory.declaration {pervasive = false, syntax = true, pos = #pos entry}
                     (fn phi => add path (morph phi candidate)) lthy
                 val _ = Navigation.defer_report installed (#pos entry)
                   (Position.make_entity_markup {def = true} identity traitN (path, #pos entry))
                 val _ = Navigation.defer_report_text installed (#pos entry) Markup.typing
                   (tooltip installed entry)
               in installed end)
        end)
      val _ = Reports.replay completed reports
    in completed end

  fun pretty_entry ctxt (entry: trait_entry) =
    Pretty.block
      ([Pretty.keyword1 "trait", Pretty.brk 1, Pretty.str (#path entry), Pretty.brk 1,
        Pretty.str "\<mapsto>", Pretty.brk 1, Syntax.pretty_sort ctxt (#sort entry)] @
       (if null (#constants entry) then [] else
         [Pretty.brk 1, Pretty.enclose "(" ")"
           (Pretty.commas (map (fn (name, {term, ...}) =>
             Pretty.block [Pretty.str name, Pretty.brk 1, Pretty.str "\<mapsto>", Pretty.brk 1,
               Syntax.pretty_term ctxt term]) (#constants entry)))]))

  fun command payload interactive lthy =
    let
      val level = Config.get lthy URust_Parser_Config.verbosity
      val _ = if 0 <= level andalso level <= 2 then ()
        else fail "verbosity must be between 0 and 2" (#2 (#path payload))
      val completed = declare payload lthy
      val _ =
        if level > 0 andalso (interactive orelse Config.get completed Proof_Display.show_results)
        then Pretty.writeln (pretty_entry completed (the (lookup completed (#1 (#path payload)))))
        else ()
    in completed end

  val named = Parse.token Parse.string >>
    (Input.source_content_range o Token.input_of #> apsnd Position.range_position)
  val constant = (named --| \<^keyword>\<open>=\<close>) -- Parse.embedded_input
  val _ =
    Outer_Syntax.local_theory' \<^command_keyword>\<open>urust_trait\<close>
      "declare a context-local Rust trait sort and associated constants"
      ((named --| \<^keyword>\<open>=\<close>) -- Parse.embedded_input --
        Scan.optional (\<^keyword>\<open>urust_consts\<close> |-- Parse.and_list1 constant) [] >>
          (fn ((path, sort), constants) =>
            command {path = path, sort = sort, constants = constants}))
end
\<close>

section\<open> Initial trait mappings \<close>

text\<open>
Marker and equality traits impose no additional HOL class requirement. Both Rust ordering trait
spellings map to \<open>ord\<close>, the operand sort of the shallow comparison operators.
\<close>

urust_trait "Copy" = \<open> type \<close>
urust_trait "Clone" = \<open> type \<close>
urust_trait "PartialEq" = \<open> type \<close>
urust_trait "Eq" = \<open> type \<close>
urust_trait "Hash" = \<open> type \<close>
urust_trait "Debug" = \<open> type \<close>
urust_trait "PartialOrd" = \<open> ord \<close>
urust_trait "Ord" = \<open> ord \<close>

end
