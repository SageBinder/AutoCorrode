theory Parser_Impl_Model_Parameters
  imports Parser_Impl_AST Parser_Utils
begin

section\<open> Explicit contextual representation parameters \<close>

text\<open>
Representation parameters have authored identities independent of Rust source generics and
computation channels. The type registry supplies the declared families and their requirements;
this component owns checked contextual bindings and their native morphism transport.
\<close>

ML\<open>
structure URust_Model_Parameters =
struct
  datatype role = Address | Global | Model of string
  type rename = (string * Position.T) * Input.source
  type binding = {typ: typ, pos: Position.T}

  fun name Address = "address"
    | name Global = "global"
    | name (Model family) = family

  fun order roles =
    filter (member (op =) roles) [Address, Global] @
      (roles |> map_filter (fn Model family => SOME family | _ => NONE)
        |> distinct (op =) |> sort_strings |> map Model)

  fun canonical Address = ("_urust_backend", 0)
    | canonical Global = ("_urust_backend", 1)
    | canonical (Model family) = ("_urust_model_" ^ family, 0)

  fun error_at message pos = error ("urust: " ^ message ^ Position.here pos)

  fun distinct_keys label renames =
    fold (fn ((key, pos), _) => fn seen =>
       (case AList.lookup (op =) seen key of
         SOME first => error ("urust: duplicate " ^ label ^ " " ^ quote key ^
           Position.here_list [pos, first])
       | NONE => (key, pos) :: seen)) renames []
    |> K ()

  fun read_type ctxt source =
    URust_Report_Transaction.native ctxt (fn read_ctxt =>
      Syntax.read_typ read_ctxt (Syntax.implode_input source)
        handle ERROR message => error_at message (Input.pos_of source))

  fun satisfies ctxt label typ sort pos =
    if Sign.of_sort (Proof_Context.theory_of ctxt) (typ, sort) then ()
    else error_at (label ^ " does not satisfy sort " ^
      Syntax.string_of_sort ctxt sort) pos

  fun merge_bindings tables = Symtab.join (fn family =>
      fn (left: binding, right: binding) =>
        if #typ left = #typ right then left
        else error ("urust: conflicting model parameter " ^ quote family ^
          Position.here_list [#pos left, #pos right])) tables
  structure Defaults = Generic_Data
  (
    type T = binding Symtab.table
    val empty = Symtab.empty
    val merge = merge_bindings
  )

  fun lookup ctxt role = Symtab.lookup (Defaults.get (Context.Proof ctxt)) (name role)

  fun read_bindings requirements ctxt renames =
    let
      val _ = distinct_keys "model parameter" renames
      fun read ((family, key_pos), source) =
        let
          val type_pos = Input.pos_of source
          val declared = filter (fn (role, _) => name role = family) requirements
          val _ = if family = "address" orelse family = "global" orelse not (null declared)
            then () else error_at ("unknown model parameter " ^ quote family) key_pos
          val typ = read_type ctxt source
          val _ = if null (Term.add_tvarsT typ []) then () else
            error_at "model bindings require checked concrete/free types or _ inference holes"
              type_pos
          (* Registry metadata establishes the family, not a global sort requirement. Unused
             mappings must not restrict a context; the lazy resolver checks each actual demand. *)
        in (family, {typ = typ, pos = type_pos}: binding) end
    in map read renames end

  fun with_bindings requirements renames ctxt =
    let val bindings = read_bindings requirements ctxt renames
    in Context.proof_map (Defaults.map (fold Symtab.update bindings)) ctxt end

  fun declaration requirements ctxt renames =
    let val bindings = read_bindings requirements ctxt renames
    in Morphism.entity (fn phi => Defaults.map
      (fold (fn (family, {typ, pos}) => Symtab.update
        (family, {typ = Morphism.typ phi typ, pos = pos})) bindings)) end

  fun inherit ctxt = Context.proof_map (Defaults.put (Defaults.get (Context.Proof ctxt)))
  val without_bindings = Context.proof_map (Defaults.put Symtab.empty)

  (* Only item preparation installs ambient connections. They never enter the resulting local
     theory. Their checked types travel with the enclosing impl's preparation context. *)
  structure Ambient = Proof_Data
  (
    type T = binding Symtab.table
    fun init _ = Symtab.empty
  )

  fun ambient ctxt rust = Symtab.lookup (Ambient.get ctxt) rust
  fun ambient_name ctxt hol_name =
    exists (fn (_, {typ, ...}: binding) =>
      case typ of TFree (name, _) => name = hol_name | _ => false) (Symtab.dest (Ambient.get ctxt))

  fun with_ambient parameters renames ctxt =
    let
      val _ = distinct_keys "ambient type parameter" renames
      fun read ((rust, key_pos), source) =
        let
          val type_pos = Input.pos_of source
          val kind = (case find_first (fn URust_AST.Generic_Parameter (name, _, _) =>
              name = rust) parameters of
            SOME (URust_AST.Generic_Parameter (_, _, kind)) => kind
          | NONE => error_at ("unknown ambient type parameter " ^ quote rust) key_pos)
          val _ = if kind = URust_AST.Type_Parameter then ()
            else error_at "ambient bindings require a Rust type parameter" key_pos
          val typ = read_type ctxt source
          val (name, sort) = (case typ of TFree pair => pair
            | _ => error_at "ambient bindings require a fixed HOL type variable" type_pos)
          val fixed_sort = (case Variable.def_sort ctxt (name, ~1) of SOME sort => sort
            | NONE => error_at ("HOL type variable " ^ quote name ^ " is not fixed") type_pos)
          val fixed = TFree (name, fixed_sort)
          val _ = satisfies ctxt "ambient type parameter" fixed sort type_pos
        in (rust, {typ = fixed, pos = type_pos}: binding) end
      val bindings = map read renames
      val names = map (fn (_, {typ = TFree (name, _), ...}) => name
        | _ => raise Fail "checked ambient binding is not a free type") bindings
      val _ = if length names = length (distinct (op =) names) then ()
        else error_at "ambient HOL parameter names must be distinct" (snd (fst (hd renames)))
    in Ambient.map (fold Symtab.update bindings) ctxt end

  fun inherit_ambient ctxt = Ambient.put (Ambient.get ctxt)
end
\<close>

end
