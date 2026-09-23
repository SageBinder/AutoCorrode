theory Parser_Impl_Printer
  imports Parser_Impl_AST
begin

section\<open> Canonical AST pretty printer \<close>

text\<open>
The printer consumes only the unresolved AST. Its abstract tokens contain no source positions, so
they are suitable both for deterministic rendering and for parse-print-parse comparisons. Serialized
mode retains explicit group nodes; human mode removes them and relies on the same precedence-aware
parenthesization used for synthetic grammar-required groups. Internally, canonical token events are
finalized once into an abstract document containing generated source text and 1-based lexeme ranges.
The public token projection discards those ranges, while the output adapter can render the same
document with report-derived markup.
\<close>

ML\<open>
signature URUST_PRINTER =
sig
  datatype mode = Serialized | Human
  type options = {mode: mode}

  val serialized_options: options
  val human_options: options

  eqtype token
  val tokens_of_expr: options -> URust_AST.ur_expr -> token list
  val tokens_of_datatype:
    options -> URust_AST.urust_datatype -> token list
  val tokens_of_function:
    options -> URust_AST.urust_function -> token list
  val pretty_tokens: token list -> Pretty.T
  val pretty_expr: options -> URust_AST.ur_expr -> Pretty.T
  val pretty_datatype:
    options -> URust_AST.urust_datatype -> Pretty.T
  val pretty_function:
    options -> URust_AST.urust_function -> Pretty.T
  val string_of_expr: options -> URust_AST.ur_expr -> string
  val string_of_datatype:
    options -> URust_AST.urust_datatype -> string
  val string_of_function:
    options -> URust_AST.urust_function -> string
end

signature URUST_PRINTER_DOCUMENT =
sig
  type document
  type lexeme =
    {text: string,
     range: int * int,
     fallback: string -> Pretty.T}

  val human_expr: URust_AST.ur_expr -> document
  val human_datatype: URust_AST.urust_datatype -> document
  val human_function: URust_AST.urust_function -> document
  val probe_text: document -> string
  val pretty: (lexeme -> Pretty.T) -> document -> Pretty.T
end

local
structure URust_Printer_Implementation =
struct
open URust_AST

datatype mode = Serialized | Human
type options = {mode: mode}

val serialized_options = {mode = Serialized}
val human_options = {mode = Human}

datatype lexical_role =
    Keyword_Role
  | Operator_Role
  | Delimiter_Role
  | Numeral_Role
  | String_Role
  | Identifier_Role
  | Embedded_Role

datatype token =
    Lexeme of lexical_role * string
  | Break of int * int
  | Forced_Break
  | Begin_Block of int * bool
  | End_Block

fun malformed message =
  error ("uRust pretty printer: " ^ message)

fun lexeme role text =
  if text = "" then malformed "empty lexeme"
  else [Lexeme (role, text)]

val keyword = lexeme Keyword_Role
val operator = lexeme Operator_Role
val delimiter = lexeme Delimiter_Role
val numeral = lexeme Numeral_Role
val string_literal = lexeme String_Role
val identifier = lexeme Identifier_Role
val embedded = lexeme Embedded_Role

val space = [Break (1, 0)]
val line = [Forced_Break]

fun block indent consistent body =
  Begin_Block (indent, consistent) :: body @ [End_Block]

fun parenthesized body =
  delimiter "(" @ block 0 false body @ delimiter ")"

fun wrap_document required actual document =
  if actual < required then parenthesized document else document

fun bracketed body =
  delimiter "[" @ block 2 false body @ delimiter "]"

fun has_forced_break body =
  exists (fn Forced_Break => true | _ => false) body

fun braced_after prefix body =
  if null body then prefix @ delimiter "{" @ delimiter "}"
  else if has_forced_break body then
    block 2 false
      (prefix @ delimiter "{" @ line @ body) @
    line @ delimiter "}"
  else
    block 0 true
      (prefix @ delimiter "{" @
       [Break (1, 2)] @
       block 0 false body @
       [Break (1, 0)] @
       delimiter "}")

fun multiline_braced_after prefix body =
  if null body then prefix @ delimiter "{" @ delimiter "}"
  else
    block 2 false
      (prefix @ delimiter "{" @ line @ body) @
    line @ delimiter "}"

fun braced body = braced_after [] body

fun comma_documents documents =
  flat (Library.separate (delimiter "," @ space) documents)

fun comma_lines documents =
  flat (Library.separate (delimiter "," @ line) documents)

fun require_nonempty what [] =
      malformed (what ^ " requires at least one member")
  | require_nonempty _ values = values

fun require_at_least what minimum values =
  if length values < minimum
  then
    malformed
      (what ^ " requires at least " ^ string_of_int minimum ^ " members")
  else values

fun require_identifier what name =
  if name = "" then malformed (what ^ " has an empty identifier")
  else name

fun require_datatype_identifier what name =
  if name = "_" then malformed (what ^ " cannot be `_`")
  else require_identifier what name

fun reject_duplicate_names what names =
  let
    fun check _ [] = ()
      | check seen (name :: rest) =
          if Symtab.defined seen name
          then malformed (what ^ " contains duplicate identifier " ^ quote name)
          else check (Symtab.update (name, ()) seen) rest
  in check Symtab.empty names end

fun unsigned_name UT_U8 = "u8"
  | unsigned_name UT_U16 = "u16"
  | unsigned_name UT_U32 = "u32"
  | unsigned_name UT_U64 = "u64"
  | unsigned_name UT_Usize = "usize"

fun signed_name ST_I32 = "i32"
  | signed_name ST_I64 = "i64"

fun primitive_name (Primitive_Unsigned unsigned) =
      unsigned_name unsigned
  | primitive_name (Primitive_Signed signed) =
      signed_name signed

fun cast_target_document (CT_Unsigned unsigned) =
      keyword (unsigned_name unsigned)
  | cast_target_document (CT_Signed signed) =
      keyword (signed_name signed)
  | cast_target_document (CT_RawPointer (mutability, unsigned)) =
      operator "*" @ space @
      keyword
        (case mutability of
           RPM_Const => "const"
         | RPM_Mut => "mut") @
      space @ keyword (unsigned_name unsigned)

fun generic_arguments_document (Generic_Args (arguments, _)) =
  let
    val arguments = require_nonempty "generic argument list" arguments
    fun argument_document (Generic_Arg (canonical, _)) =
      if canonical = ""
      then malformed "generic argument has empty canonical text"
      else embedded canonical
  in
    delimiter "::<" @
    block 2 false (comma_documents (map argument_document arguments)) @
    delimiter ">"
  end

fun segment_document role (Path_Segment (name, _, arguments)) =
  lexeme role (require_identifier "path segment" name) @
  (case arguments of
     NONE => []
   | SOME generic_arguments =>
       generic_arguments_document generic_arguments)

fun path_document (UR_Path (head, segments, _)) =
  let
    val segments = require_nonempty "path" segments
    val _ =
      (case head of
         Identifier_Head => ()
       | Primitive_Head primitive =>
           (case segments of
              Path_Segment (name, _, NONE) :: _ :: _ =>
                if name = primitive_name primitive then ()
                else
                  malformed
                    ("primitive path head " ^ quote name ^
                      " does not match its primitive tag")
            | [_] =>
                malformed
                  "primitive path requires an associated-item segment"
            | Path_Segment (_, _, SOME _) :: _ =>
                malformed
                  "primitive path head cannot carry generic arguments"
            | [] => malformed "path requires at least one member"))
    fun documents _ [] = []
      | documents index (segment :: rest) =
          let
            val role =
              (case (head, index) of
                 (Primitive_Head _, 0) => Keyword_Role
               | (Identifier_Head, 0) => Identifier_Role
               | _ => Identifier_Role)
            val current = segment_document role segment
          in
            current ::
              (if null rest then []
               else delimiter "::" :: documents (index + 1) rest)
          end
  in
    flat (documents 0 segments)
  end

fun identifier_head_path what path =
  (case path_head path of
     Identifier_Head => path_document path
   | Primitive_Head _ =>
       malformed (what ^ " cannot use a primitive path head"))

fun single_plain_path path =
  (case (path_head path, path_segments path) of
     (Identifier_Head, [Path_Segment (name, _, NONE)]) => SOME name
   | _ => NONE)

fun value_antiquotation source =
  delimiter "\<llangle>" @
  embedded (Input.string_of source) @
  delimiter "\<rrangle>"

fun expression_antiquotation source =
  lexeme Embedded_Role "\<epsilon>" @
  delimiter "\<open>" @
  embedded (Input.string_of source) @
  delimiter "\<close>"

fun literal_document (LP_Integer integer) =
      numeral (integer_literal_lexeme integer)
  | literal_document (LP_Bool (value, _)) =
      keyword (if value then "true" else "false")
  | literal_document (LP_String (raw, _)) =
      string_literal raw
  | literal_document (LP_ValAntiq antiquotation) =
      value_antiquotation
        (value_antiquotation_source antiquotation)

fun binop_text Add = "+"
  | binop_text Sub = "-"
  | binop_text Mul = "*"
  | binop_text Div = "/"
  | binop_text Mod = "%"
  | binop_text Shl = "<<"
  | binop_text Shr = ">>"
  | binop_text BAnd = "&"
  | binop_text BOr = "|"
  | binop_text BXor = "^"
  | binop_text Eq = "=="
  | binop_text Ne = "!="
  | binop_text Lt = "<"
  | binop_text Le = "<="
  | binop_text Gt = ">"
  | binop_text Ge = ">="
  | binop_text And = "&&"
  | binop_text Or = "||"

fun assignop_text Assign = "="
  | assignop_text AssignAdd = "+="
  | assignop_text (AssignBin AssignSub) = "-="
  | assignop_text (AssignBin AssignMul) = "*="
  | assignop_text (AssignBin AssignMod) = "%="
  | assignop_text (AssignBin AssignBAnd) = "&="
  | assignop_text (AssignBin AssignBOr) = "|="
  | assignop_text (AssignBin AssignBXor) = "^="
  | assignop_text (AssignBin AssignShl) = "<<="
  | assignop_text (AssignBin AssignShr) = ">>="

fun range_text RK_Exclusive = ".."
  | range_text RK_Inclusive = "..="

val expression_body_precedence = 0
val low_expression_precedence = 1
val assignment_precedence = 2
val range_precedence = 3
val logical_or_precedence = 4
val logical_and_precedence = 5
val comparison_precedence = 6
val bit_or_precedence = 7
val bit_xor_precedence = 8
val bit_and_precedence = 9
val shift_precedence = 10
val additive_precedence = 11
val multiplicative_precedence = 12
val cast_precedence = 13
val prefix_precedence = 14
val postfix_precedence = 15
val primary_precedence = 16

fun binop_precedence Or = logical_or_precedence
  | binop_precedence And = logical_and_precedence
  | binop_precedence Eq = comparison_precedence
  | binop_precedence Ne = comparison_precedence
  | binop_precedence Lt = comparison_precedence
  | binop_precedence Le = comparison_precedence
  | binop_precedence Gt = comparison_precedence
  | binop_precedence Ge = comparison_precedence
  | binop_precedence BOr = bit_or_precedence
  | binop_precedence BXor = bit_xor_precedence
  | binop_precedence BAnd = bit_and_precedence
  | binop_precedence Shl = shift_precedence
  | binop_precedence Shr = shift_precedence
  | binop_precedence Add = additive_precedence
  | binop_precedence Sub = additive_precedence
  | binop_precedence Mul = multiplicative_precedence
  | binop_precedence Div = multiplicative_precedence
  | binop_precedence Mod = multiplicative_precedence

fun comparison_operator Eq = true
  | comparison_operator Ne = true
  | comparison_operator Lt = true
  | comparison_operator Le = true
  | comparison_operator Gt = true
  | comparison_operator Ge = true
  | comparison_operator _ = false

val pattern_or_precedence = 1
val pattern_alias_precedence = 2
val pattern_range_precedence = 3
val pattern_prefix_precedence = 4
val pattern_atom_precedence = 5

fun mode_is_serialized ({mode = Serialized}: options) = true
  | mode_is_serialized _ = false

fun is_unit (UE_Unit _) = true
  | is_unit _ = false

fun fuel_document source =
  delimiter "#" @ delimiter "[" @ keyword "fuel" @ delimiter "(" @
  expression_antiquotation source @ delimiter ")" @ delimiter "]"

fun function_arity_document arity =
  if 1 <= arity andalso arity <= 14 then
    String.concat
      (map (fn digit => "\<^sub>" ^ str digit)
        (String.explode (string_of_int arity)))
    |> delimiter
  else
    malformed
      ("function-literal arity " ^ string_of_int arity ^
        " is outside the supported range 1 through 14")

fun repeat_operator_precedence Add = additive_precedence
  | repeat_operator_precedence Sub = additive_precedence
  | repeat_operator_precedence Mul = multiplicative_precedence
  | repeat_operator_precedence Div = multiplicative_precedence
  | repeat_operator_precedence Mod = multiplicative_precedence
  | repeat_operator_precedence operator =
      malformed
        ("array repeat length cannot use operator " ^
          quote (binop_text operator))

fun repeat_length_document options required repeat_length =
  (case repeat_length of
     RL_Integer integer =>
       wrap_document required primary_precedence
         (numeral (integer_literal_lexeme integer))
   | RL_Path path =>
       wrap_document required primary_precedence (path_document path)
   | RL_Bin (operator_tag, left, right, _) =>
       let
         val precedence = repeat_operator_precedence operator_tag
         val left_document =
           repeat_length_document options precedence left
         val right_document =
           repeat_length_document options (precedence + 1) right
         val document =
           block 2 false
             (left_document @ space @ operator (binop_text operator_tag) @
              space @ right_document)
       in wrap_document required precedence document end
   | RL_Group (inner, _) =>
       if mode_is_serialized options
       then wrap_document required primary_precedence
         (parenthesized
           (repeat_length_document options expression_body_precedence inner))
       else repeat_length_document options required inner
   | RL_CastUsize (inner, _) =>
       let
         val document =
           block 2 false
             (repeat_length_document options cast_precedence inner @
              space @ keyword "as" @ space @ keyword "usize")
       in wrap_document required cast_precedence document end)

fun datatype_primitive_name DPT_U8 = "u8"
  | datatype_primitive_name DPT_U16 = "u16"
  | datatype_primitive_name DPT_U32 = "u32"
  | datatype_primitive_name DPT_U64 = "u64"
  | datatype_primitive_name DPT_U128 = "u128"
  | datatype_primitive_name DPT_Usize = "usize"
  | datatype_primitive_name DPT_I8 = "i8"
  | datatype_primitive_name DPT_I16 = "i16"
  | datatype_primitive_name DPT_I32 = "i32"
  | datatype_primitive_name DPT_I64 = "i64"
  | datatype_primitive_name DPT_I128 = "i128"
  | datatype_primitive_name DPT_Isize = "isize"
  | datatype_primitive_name DPT_Bool = "bool"
  | datatype_primitive_name DPT_Char = "char"
  | datatype_primitive_name DPT_Str = "str"
  | datatype_primitive_name DPT_Never = "!"
  | datatype_primitive_name DPT_Unit = "()"

fun rust_type_document rust_type =
  let
    fun generic_argument_document argument =
      (case argument of
         Rust_Type_Argument typ => rust_type_document typ
       | Rust_Numeric_Argument integer =>
           numeral (integer_literal_lexeme integer))
    fun segment_document
        (Rust_Type_Path_Segment (name, _, arguments, _)) =
      identifier (require_identifier "Rust type path segment" name) @
      (case arguments of
         NONE => []
       | SOME values =>
           delimiter "<" @
           comma_documents (map generic_argument_document values) @
           delimiter ">")
    fun path_document segments =
      let
        fun documents [] = []
          | documents [segment] = segment_document segment
          | documents (segment :: rest) =
              segment_document segment @ delimiter "::" @
              documents rest
      in documents (require_nonempty "Rust type path" segments) end
  in
  (case rust_type of
     Primitive_Type (DPT_Unit, _) =>
       delimiter "(" @ delimiter ")"
   | Primitive_Type (DPT_Never, _) =>
       delimiter "!"
   | Primitive_Type (primitive, _) =>
       keyword (datatype_primitive_name primitive)
   | Path_Type (segments, _) =>
       path_document segments
   | Tuple_Type (types, _) =>
       parenthesized
         (case types of
            [typ] =>
              rust_type_document typ @ delimiter ","
          | _ =>
              comma_documents
                (map rust_type_document
                  (require_nonempty "Rust tuple type" types)))
   | Group_Type (typ, _) =>
       parenthesized (rust_type_document typ)
   | Reference_Type (mode, typ, _) =>
       operator "&" @
       (case mode of
          BM_Imm => []
        | BM_Mut => space @ keyword "mut") @
       space @ rust_type_document typ
   | Raw_Pointer_Type (mutability, typ, _) =>
       operator "*" @
       (case mutability of
          RPM_Const => keyword "const"
        | RPM_Mut => keyword "mut") @
       space @ rust_type_document typ
   | Slice_Type (typ, _) =>
       bracketed (rust_type_document typ)
   | Array_Type (typ, integer, _) =>
       bracketed
         (rust_type_document typ @ delimiter ";" @ space @
          numeral (integer_literal_lexeme integer))
   | HOL_Type_Source source =>
       let
         val body = Input.string_of source
         val _ =
           if body = ""
           then malformed "HOL datatype type source is empty"
           else ()
       in
         lexeme Embedded_Role "\<tau>" @
         delimiter Symbol.open_ @
         embedded body @
         delimiter Symbol.close
       end)
  end

fun datatype_shape_arity Unit_Shape = 0
  | datatype_shape_arity (Tuple_Shape types) = length types
  | datatype_shape_arity (Named_Shape fields) = length fields

fun validate_datatype_shape what shape =
  let
    val arity = datatype_shape_arity shape
    val _ =
      (case shape of
         Unit_Shape => ()
       | Tuple_Shape [] =>
           malformed (what ^ " has an empty tuple shape")
       | Tuple_Shape _ => ()
       | Named_Shape [] =>
           malformed (what ^ " has an empty named shape")
       | Named_Shape fields =>
           let
             val names =
               map
                 (fn Datatype_Field (name, _, _) =>
                   require_datatype_identifier
                     (what ^ " field") name)
                 fields
           in reject_duplicate_names (what ^ " named shape") names end)
    val _ =
      if arity <= 14 then ()
      else
        malformed
          (what ^ " has " ^ string_of_int arity ^
            " members; at most 14 are supported")
  in () end

fun datatype_shape_after options what prefix shape =
  let
    val _ = validate_datatype_shape what shape
    fun field_document (Datatype_Field (name, _, datatype_type)) =
      identifier
        (require_datatype_identifier
          (what ^ " field") name) @
      delimiter ":" @ space @
      rust_type_document datatype_type
    fun named_body fields =
      if mode_is_serialized options
      then comma_documents (map field_document fields)
      else comma_lines (map field_document fields)
  in
    (case shape of
       Unit_Shape => prefix
     | Tuple_Shape types =>
         prefix @
         parenthesized
           (comma_documents
             (map rust_type_document types))
     | Named_Shape fields =>
         if mode_is_serialized options
         then braced_after (prefix @ space) (named_body fields)
         else
           multiline_braced_after
             (prefix @ space) (named_body fields))
  end

fun datatype_variant_document options
    (Datatype_Variant (name, _, shape)) =
  let
    val name =
      require_datatype_identifier "datatype variant" name
  in
    datatype_shape_after options
      ("datatype variant " ^ quote name)
      (identifier name) shape
  end

fun datatype_document options item =
  (case item of
     Struct_Item (name, _, shape, _) =>
       let
         val name =
           require_datatype_identifier "datatype item" name
       in
         datatype_shape_after options
           ("struct " ^ quote name)
           (keyword "struct" @ space @ identifier name)
           shape @
         (case shape of
            Unit_Shape => delimiter ";"
          | Tuple_Shape _ => delimiter ";"
          | Named_Shape _ => [])
       end
   | Enum_Item (name, _, variants, _) =>
       let
         val name =
           require_datatype_identifier "datatype item" name
         val variants =
           require_nonempty "enum declaration" variants
         val variant_names =
           map
             (fn Datatype_Variant (variant_name, _, _) =>
               require_datatype_identifier
                 "datatype variant" variant_name)
             variants
         val _ =
           reject_duplicate_names
             ("enum " ^ quote name) variant_names
         val body =
           if mode_is_serialized options
           then comma_documents
             (map (datatype_variant_document options) variants)
           else comma_lines
             (map (datatype_variant_document options) variants)
       in
         if mode_is_serialized options
         then
           braced_after
             (keyword "enum" @ space @ identifier name @ space)
             body
         else
           multiline_braced_after
             (keyword "enum" @ space @ identifier name @ space)
             body
       end)

fun pattern_document options required pattern =
  let
    fun pattern_identifier what name =
      identifier (require_identifier what name)
    fun starts_with_borrow (P_Borrow _) = true
      | starts_with_borrow (P_Group (inner, _)) =
          not (mode_is_serialized options) andalso starts_with_borrow inner
      | starts_with_borrow _ = false
    fun field_document (SF_Field (name, _, inner)) =
          identifier (require_identifier "struct-pattern field" name) @
          delimiter ":" @ space @
          pattern_document options
            pattern_or_precedence inner
      | field_document (SF_Shorthand (name, _)) =
          pattern_identifier "struct-pattern shorthand" name
      | field_document (SF_Rest _) =
          operator ".."
    fun slice_document (SI_Pat inner) =
          pattern_document options
            pattern_or_precedence inner
      | slice_document (SI_Rest _) =
          operator ".."
  in
    (case pattern of
       P_Wild _ =>
         wrap_document required pattern_atom_precedence (identifier "_")
     | P_Ident (name, _) =>
         wrap_document required pattern_atom_precedence
           (pattern_identifier "pattern" name)
     | P_Path path =>
         let
           val _ =
             (case single_plain_path path of
                SOME _ =>
                  malformed
                    "P_Path cannot contain a single nongeneric identifier"
              | NONE => ())
         in
           wrap_document required pattern_atom_precedence
             (path_document path)
         end
     | P_Literal payload =>
         wrap_document required pattern_atom_precedence
           (literal_document payload)
     | P_Constr (path, arguments, _) =>
         let
           val arguments =
             require_nonempty "constructor pattern" arguments
           val document =
             identifier_head_path "constructor pattern" path @
             parenthesized
               (comma_documents
                 (map
                   (pattern_document options
                     pattern_or_precedence)
                   arguments))
         in wrap_document required pattern_atom_precedence document end
     | P_Tuple (members, _) =>
         let
           val members = require_at_least "tuple pattern" 2 members
           val document =
             parenthesized
               (comma_documents
                 (map
                   (pattern_document options
                     pattern_or_precedence)
                   members))
         in wrap_document required pattern_atom_precedence document end
     | P_Group (inner, _) =>
         if mode_is_serialized options
         then
           wrap_document required pattern_atom_precedence
             (parenthesized
               (pattern_document options
                 pattern_or_precedence inner))
         else pattern_document options required inner
     | P_Borrow (borrow_mode, inner, _) =>
         let
           val prefix =
             (case borrow_mode of
                BM_Imm => operator "&"
              | BM_Mut => operator "&" @ space @ keyword "mut")
           val document =
             prefix @
             (case borrow_mode of
                BM_Imm => if starts_with_borrow inner then space else []
              | BM_Mut => space) @
             pattern_document options
               pattern_prefix_precedence inner
         in wrap_document required pattern_prefix_precedence document end
     | P_Alias (name, _, inner, _) =>
         let
           val document =
             block 2 false
               (identifier
                  (require_identifier "pattern alias" name) @
                space @ operator "@" @ space @
                pattern_document options
                  pattern_alias_precedence inner)
         in wrap_document required pattern_alias_precedence document end
     | P_Range (range_kind, left, right, _) =>
         let
           val document =
             block 2 false
               (pattern_document options
                  pattern_range_precedence left @
                space @ operator (range_text range_kind) @ space @
                pattern_document options
                  (pattern_range_precedence + 1) right)
         in wrap_document required pattern_range_precedence document end
     | P_Slice (items, _) =>
         wrap_document required pattern_atom_precedence
           (bracketed
             (comma_documents (map slice_document items)))
     | P_Struct (path, fields, _) =>
         let
           val fields = require_nonempty "struct pattern" fields
           val document =
             braced_after
               (identifier_head_path "struct pattern" path @ space)
               (comma_lines (map field_document fields))
         in wrap_document required pattern_atom_precedence document end
     | P_Or (alternatives, _) =>
         let
           val alternatives =
             require_at_least "or-pattern" 2 alternatives
           val document =
             block 2 false
               (flat
                 (Library.separate (space @ operator "|" @ space)
                   (map
                     (pattern_document options
                       pattern_alias_precedence)
                     alternatives)))
         in wrap_document required pattern_or_precedence document end)
  end

fun source_cast_target_document (SCT_Primitive (target, _)) =
      cast_target_document target
  | source_cast_target_document (SCT_Named path) =
      identifier_head_path "named cast target" path

fun no_struct_requires_group options expression =
  let
    fun place_violation (UP_Path _) = false
      | place_violation (UP_Deref (operand, _)) = expression_violation operand
      | place_violation (UP_Field (base, _, _)) = place_violation base
      | place_violation (UP_Index (base, _, _)) = place_violation base
      | place_violation (UP_Antiq _) = false
    and callee_violation (UC_Path _) = false
      | callee_violation (UC_Method (receiver, _)) =
          expression_violation receiver
      | callee_violation (UC_Antiq _) = false
      | callee_violation (UC_FunLiteral _) = false
    and expression_violation expression =
      (case expression of
         UE_Struct _ => true
       | UE_Group (inner, _) =>
           if mode_is_serialized options then false
           else expression_violation inner
       | UE_Return (NONE, _) => true
       | UE_Return (SOME value, _) => expression_violation value
       | UE_Closure (_, body, _) => expression_violation body
       | UE_Bin (_, left, right, _) =>
           expression_violation left orelse expression_violation right
       | UE_Cast (operand, _, _) => expression_violation operand
       | UE_Unary (_, operand, _) => expression_violation operand
       | UE_Range (_, left, right, _) =>
           expression_violation left orelse expression_violation right
       | UE_Assign (_, place, right, _) =>
           place_violation place orelse expression_violation right
       | UE_Call (callee, _, _) => callee_violation callee
       | UE_Field (receiver, _, _) => expression_violation receiver
       | UE_Index (receiver, _, _) => expression_violation receiver
       | UE_TupleProjection (receiver, _, _) =>
           expression_violation receiver
       | UE_Let _ => true
       | UE_LetMut _ => true
       | UE_Const _ => true
       | UE_Seq _ => true
       | _ => false)
  in expression_violation expression end

fun expression_document options required expression =
  let
    fun block_body what block_expression =
      (case block_expression of
         UE_Block (inner, _) =>
           if is_unit inner then []
           else
             expression_document options
               expression_body_precedence inner
       | _ => malformed (what ^ " requires a block"))

    fun code_braced_after prefix body =
      if mode_is_serialized options
      then braced_after prefix body
      else multiline_braced_after prefix body

    fun required_block what block_expression =
      code_braced_after [] (block_body what block_expression)

    fun required_block_after prefix what block_expression =
      code_braced_after prefix
        (block_body what block_expression)

    fun expression_after prefix required expression =
      (case expression of
         UE_Block _ =>
           required_block_after prefix
             "expression block" expression
       | _ =>
           prefix @
           expression_document options required expression)

    fun no_struct expression =
      if no_struct_requires_group options expression
      then parenthesized
        (expression_document options
          expression_body_precedence expression)
      else
        expression_document options
          low_expression_precedence expression

    fun expression_list expressions =
      comma_documents
        (map
          (expression_document options
            low_expression_precedence)
          expressions)

    fun place_document required place =
      (case place of
         UP_Path path =>
           if is_primitive_path path
           then malformed "assignment place cannot use a primitive path"
           else
             wrap_document required primary_precedence
               (path_document path)
       | UP_Deref (operand, _) =>
           wrap_document required prefix_precedence
             (operator "*" @
              expression_document options
                prefix_precedence operand)
       | UP_Field (base, name, _) =>
           wrap_document required postfix_precedence
             (place_document postfix_precedence base @ delimiter "." @
              identifier
                (require_identifier "assignment field" name))
       | UP_Index (base, index, _) =>
           wrap_document required postfix_precedence
             (place_document postfix_precedence base @
              bracketed
                (expression_document options
                  low_expression_precedence index))
       | UP_Antiq source =>
           wrap_document required primary_precedence
             (expression_antiquotation source))

    fun callee_document callee arguments =
      let
        val argument_document =
          parenthesized (expression_list arguments)
      in
        (case callee of
           UC_Path path =>
             (primary_precedence,
              path_document path @ argument_document)
         | UC_Method (receiver, segment) =>
             (postfix_precedence,
              expression_document options
                postfix_precedence receiver @
              delimiter "." @
              segment_document Identifier_Role segment @
              argument_document)
         | UC_Antiq source =>
             (primary_precedence,
              expression_antiquotation source @ argument_document)
         | UC_FunLiteral
             (antiquotation, arity, _, generic_arguments) =>
             (primary_precedence,
              value_antiquotation
                (value_antiquotation_source antiquotation) @
              function_arity_document arity @
              (case generic_arguments of
                 NONE => []
               | SOME arguments =>
                   generic_arguments_document arguments) @
              argument_document))
      end

    fun struct_expression_field_document (SE_Field (name, _, value)) =
      expression_after
        (identifier (require_identifier "struct-expression field" name) @
         delimiter ":" @ space)
        expression_body_precedence value

    fun log_data_entry_document (LDE_String (raw, _)) =
          string_literal raw
      | log_data_entry_document (LDE_Identifier (name, _)) =
          identifier (require_identifier "logging-data entry" name)

    fun arm_document (UR_Arm (pattern, guard, body, _)) =
      let
        val prefix =
          pattern_document options pattern_or_precedence pattern @
          (case guard of
             NONE => []
           | SOME (guard_expression, _) =>
               space @ keyword "if" @ space @
               expression_document options
                 expression_body_precedence guard_expression) @
          space @ delimiter "=>" @ space
      in
        expression_after prefix low_expression_precedence body
      end

    fun binding_statement_document prefix pattern value body =
      expression_after
        (prefix @ space @
         pattern_document options
           pattern_or_precedence pattern @
         space @ delimiter "=" @ space)
        low_expression_precedence value @
      delimiter ";" @ line @
      expression_document options
        expression_body_precedence body

    fun conditional_document leading expression =
      let
        fun finish
              success_name fallback_name fallback_message
              head success fallback =
          let
            val success_body =
              block_body success_name success
            val fallback_prefix =
              delimiter "}" @ space @ keyword "else" @ space
          in
            (case fallback of
               NONE => code_braced_after head success_body
             | SOME alternative =>
                 (case alternative of
                    UE_Block _ =>
                      let
                        val alternative_body =
                          block_body fallback_name alternative
                      in
                        if mode_is_serialized options andalso
                            not (has_forced_break success_body orelse
                              has_forced_break alternative_body)
                        then
                          braced_after head success_body @
                          space @ keyword "else" @ space @
                          braced alternative_body
                        else
                          block 2 false
                            (head @ delimiter "{" @ line @ success_body) @
                          line @
                          code_braced_after
                            fallback_prefix alternative_body
                      end
                  | UE_If _ =>
                      block 2 false
                        (head @ delimiter "{" @ line @ success_body) @
                      line @
                      conditional_document fallback_prefix alternative
                  | UE_IfLet _ =>
                      block 2 false
                        (head @ delimiter "{" @ line @ success_body) @
                      line @
                      conditional_document fallback_prefix alternative
                  | _ =>
                      malformed fallback_message))
          end
      in
        (case expression of
           UE_If (condition, success, fallback, _) =>
             finish
               "if success branch"
               "if fallback"
               "if fallback must be a block or conditional"
               (leading @ keyword "if" @ space @
                no_struct condition @ space)
               success fallback
         | UE_IfLet (pattern, value, success, fallback, _) =>
             finish
               "if-let success branch"
               "if-let fallback"
               "if-let fallback must be a block or conditional"
               (leading @ keyword "if" @ space @ keyword "let" @ space @
                pattern_document options
                  pattern_or_precedence pattern @
                space @ delimiter "=" @ space @
                no_struct value @ space)
               success fallback
         | _ => malformed "internal non-conditional fallback")
      end

    fun body_document expression =
      (case expression of
         UE_Let (pattern, value, body, _) =>
           binding_statement_document
             (keyword "let") pattern value body
       | UE_LetMut (pattern, value, body, _) =>
           binding_statement_document
             (keyword "let" @ space @ keyword "mut")
             pattern value body
       | UE_Const (pattern, value, body, _) =>
           binding_statement_document
             (keyword "const") pattern value body
       | UE_LetElse
           (pattern, value, fallback, continuation, _) =>
           required_block_after
             (keyword "let" @ space @
              pattern_document options
                pattern_or_precedence pattern @
              space @ delimiter "=" @ space @
              expression_document options
                low_expression_precedence value @
              space @ keyword "else" @ space)
             "let-else fallback" fallback @
           delimiter ";" @ line @
           expression_document options
             expression_body_precedence continuation
       | UE_Seq (first, second, _) =>
           if is_unit second then
             (case first of
                UE_Return _ =>
                  malformed
                    "terminal return cannot be represented as UE_Seq (_, UE_Unit _)"
              | _ =>
                  expression_document options
                    low_expression_precedence first @ delimiter ";")
           else
             expression_document options
               low_expression_precedence first @
             delimiter ";" @ line @
             expression_document options
               expression_body_precedence second
       | _ =>
           expression_document_raw expression)

    and expression_document_raw expression =
      (case expression of
         UE_Unit _ =>
           wrap_document required primary_precedence
             (delimiter "(" @ delimiter ")")
       | UE_Tuple (members, _) =>
           let
             val members = require_at_least "tuple expression" 2 members
           in
             wrap_document required primary_precedence
               (parenthesized (expression_list members))
           end
       | UE_Array (members, _) =>
           wrap_document required primary_precedence
             (bracketed (expression_list members))
       | UE_ArrayRepeat (repeat_mode, value, repeat_length, _) =>
           let
             val value_document =
               (case repeat_mode of
                  AR_Ordinary =>
                    expression_document options
                      low_expression_precedence value
                | AR_InlineConst =>
                    keyword "const" @ space @
                    required_block
                      "inline-const array repeat operand" value)
           in
             wrap_document required primary_precedence
               (bracketed
                 (value_document @ delimiter ";" @ space @
                  repeat_length_document options
                    expression_body_precedence repeat_length))
           end
       | UE_Struct (path, fields, _) =>
           wrap_document required primary_precedence
             (braced_after
               (identifier_head_path "struct expression" path @ space)
               (comma_lines
                 (map struct_expression_field_document fields)))
       | UE_Path path =>
           wrap_document required primary_precedence (path_document path)
       | UE_Literal payload =>
           wrap_document required primary_precedence
             (literal_document payload)
       | UE_ExprAntiq source =>
           wrap_document required primary_precedence
             (expression_antiquotation source)
       | UE_Yield _ =>
           wrap_document required primary_precedence
             (keyword "\<y>\<i>\<e>\<l>\<d>")
       | UE_Log (priority, data, _) =>
           wrap_document required primary_precedence
             (keyword "\<l>\<o>\<g>" @ space @
              value_antiquotation
                (value_antiquotation_source priority) @ space @
              value_antiquotation
                (value_antiquotation_source data))
       | UE_LogData (entries, _) =>
           let
             val entries =
               require_nonempty "primitive logging-data expression" entries
           in
             wrap_document required primary_precedence
               (keyword "l" @ delimiter "\<llangle>" @
                block 2 false
                  (comma_documents
                    (map log_data_entry_document entries)) @
                delimiter "\<rrangle>")
           end
       | UE_Closure (formals, body, _) =>
           let
             fun formal_document (P_Ident (name, _)) =
                   identifier
                     (require_identifier "closure formal" name)
               | formal_document (P_Wild _) =
                   identifier "_"
               | formal_document _ =
                   malformed
                     "closure formals must be identifiers or wildcards"
             val bars =
               if null formals
               then operator "||"
               else
                 operator "|" @
                 comma_documents (map formal_document formals) @
                 operator "|"
             val document =
               expression_after
                 (bars @ space)
                 low_expression_precedence body
           in
             wrap_document required low_expression_precedence document
           end
       | UE_Let _ =>
           wrap_document required expression_body_precedence
             (body_document expression)
       | UE_LetMut _ =>
           wrap_document required expression_body_precedence
             (body_document expression)
       | UE_Const _ =>
           wrap_document required expression_body_precedence
             (body_document expression)
       | UE_Seq _ =>
           wrap_document required expression_body_precedence
             (body_document expression)
       | UE_Return (value, _) =>
           let
             val document =
               keyword "return" @
               (case value of
                  NONE => []
                | SOME returned =>
                    space @
                    expression_document options
                      low_expression_precedence returned)
           in
             wrap_document required low_expression_precedence document
           end
       | UE_Bin (operator_tag, left, right, _) =>
           let
             val precedence = binop_precedence operator_tag
             val child_precedence =
               if comparison_operator operator_tag
               then precedence + 1
               else precedence
             val right_precedence = precedence + 1
             val document =
               block 2 false
                 (expression_document options
                    child_precedence left @
                  space @ operator (binop_text operator_tag) @ space @
                  expression_document options
                    right_precedence right)
           in wrap_document required precedence document end
       | UE_Cast (operand, target, _) =>
           let
             val document =
               block 2 false
                 (expression_document options
                    cast_precedence operand @
                  space @ keyword "as" @ space @
                  source_cast_target_document target)
           in wrap_document required cast_precedence document end
       | UE_Unary (U_Propagate, operand, _) =>
           wrap_document required postfix_precedence
             (expression_document options
                postfix_precedence operand @
              operator "?")
       | UE_Unary (unary_operator, operand, _) =>
           let
             val prefix =
               (case unary_operator of
                  U_Not => operator "!"
                | U_Borrow BM_Imm => operator "&"
                | U_Borrow BM_Mut =>
                    operator "&" @ space @ keyword "mut" @ space
                | U_Deref => operator "*"
                | U_Propagate =>
                    malformed "internal postfix operator dispatch")
           in
             wrap_document required prefix_precedence
               (prefix @
                expression_document options
                  prefix_precedence operand)
           end
       | UE_Group (inner, _) =>
           if mode_is_serialized options
           then
             wrap_document required primary_precedence
               (parenthesized
                 (expression_document options
                   expression_body_precedence inner))
           else expression_document options required inner
       | UE_Block (inner, _) =>
           wrap_document required primary_precedence
             (if is_unit inner then braced []
              else
                braced
                  (expression_document options
                    expression_body_precedence inner))
       | UE_If (condition, success, fallback, _) =>
           wrap_document required primary_precedence
             (conditional_document [] expression)
       | UE_IfLet (pattern, value, success, fallback, _) =>
           wrap_document required primary_precedence
             (conditional_document [] expression)
       | UE_LetElse _ =>
           wrap_document required expression_body_precedence
             (body_document expression)
       | UE_While (fuel, condition, body, _) =>
           wrap_document required primary_precedence
             (required_block_after
               (fuel_document fuel @ space @ keyword "while" @ space @
                parenthesized
                  (expression_document options
                    low_expression_precedence condition) @ space)
               "while body" body)
       | UE_Loop (fuel, body, _) =>
           wrap_document required primary_precedence
             (required_block_after
               (fuel_document fuel @ space @ keyword "loop" @ space)
               "loop body" body)
       | UE_For (pattern, iterable, body, _) =>
           wrap_document required primary_precedence
             (required_block_after
               (keyword "for" @ space @
                pattern_document options
                  pattern_or_precedence pattern @
                space @ keyword "in" @ space @
                no_struct iterable @ space)
               "for body" body)
       | UE_WhileLet (fuel, pattern, value, body, _) =>
           wrap_document required primary_precedence
             (required_block_after
               (fuel_document fuel @ space @ keyword "while" @ space @
                keyword "let" @ space @
                pattern_document options
                  pattern_or_precedence pattern @
                space @ delimiter "=" @ space @
                no_struct value @ space)
               "while-let body" body)
       | UE_Call (callee, arguments, _) =>
           let val (precedence, document) =
             callee_document callee arguments
           in wrap_document required precedence document end
       | UE_Field (receiver, name, _) =>
           wrap_document required postfix_precedence
             (expression_document options
                postfix_precedence receiver @
              delimiter "." @
              identifier (require_identifier "field" name))
       | UE_Index (receiver, index, _) =>
           wrap_document required postfix_precedence
             (expression_document options
                postfix_precedence receiver @
              bracketed
                (expression_document options
                  low_expression_precedence index))
       | UE_TupleProjection (receiver, index, _) =>
           if 0 <= index andalso index <= 15 then
             wrap_document required postfix_precedence
               (expression_document options
                  postfix_precedence receiver @
                delimiter "." @ numeral (string_of_int index))
           else
             malformed
               ("tuple projection index " ^ string_of_int index ^
                 " is outside the supported range 0 through 15")
       | UE_Range (range_kind, left, right, _) =>
           let
             val document =
               block 2 false
                 (expression_document options
                    logical_or_precedence left @
                  space @ operator (range_text range_kind) @ space @
                  expression_document options
                    logical_or_precedence right)
           in wrap_document required range_precedence document end
       | UE_Assign (assignment, place, right, _) =>
           let
             val document =
               block 2 false
                 (expression_after
                   (place_document range_precedence place @
                    space @ operator (assignop_text assignment) @ space)
                   low_expression_precedence right)
           in wrap_document required assignment_precedence document end
       | UE_Macro (path, payload, _) =>
           let
             val path_name = single_plain_path path
             val document =
               (case payload of
                  MP_Arguments arguments =>
                    let
                      val _ =
                        if path_name = SOME "matches"
                        then
                          malformed
                            "matches! requires the dedicated expression/pattern payload"
                        else ()
                    in
                      identifier_head_path "macro" path @
                      operator "!" @
                      parenthesized
                        (comma_documents
                          (map
                            (expression_document options
                              expression_body_precedence)
                            arguments))
                    end
                | MP_Matches (scrutinee, pattern) =>
                    let
                      val _ =
                        if path_name = SOME "matches" then ()
                        else
                          malformed
                            "MP_Matches requires the exact matches! macro head"
                    in
                      keyword "matches" @ operator "!" @
                      parenthesized
                        (expression_document options
                           low_expression_precedence scrutinee @
                         delimiter "," @ space @
                         pattern_document options
                           pattern_or_precedence pattern)
                    end)
           in wrap_document required primary_precedence document end
       | UE_Match (match_flavour, scrutinee, arms, _) =>
           let
             val arms = require_nonempty "match expression" arms
             val match_keyword =
               (case match_flavour of
                  MF_Switch => "match_switch"
                | MF_Case => "match_case"
                | MF_Auto => "match")
           in
             wrap_document required primary_precedence
               (code_braced_after
                 (keyword match_keyword @ space @
                  no_struct scrutinee @ space)
                 (comma_lines (map arm_document arms)))
           end)
    fun body_constructor (UE_Let _) = true
      | body_constructor (UE_LetMut _) = true
      | body_constructor (UE_Const _) = true
      | body_constructor (UE_LetElse _) = true
      | body_constructor (UE_Seq _) = true
      | body_constructor _ = false
  in
    if body_constructor expression andalso
        expression_body_precedence < required
    then parenthesized (body_document expression)
    else body_document expression
  end

fun events_of_expr options expression =
  expression_document options expression_body_precedence expression

fun events_of_datatype options item =
  datatype_document options item

fun function_document options
    (Function_Item
      (name, _, parameters, return_type, body, _)) =
  let
    val name = require_identifier "function item" name
    fun parameter_document
        (Function_Parameter (mutable_pos, pattern, typ, _)) =
      (case mutable_pos of
         SOME _ => keyword "mut" @ space
       | NONE => []) @
      pattern_document options pattern_or_precedence pattern @
      delimiter ":" @ space @ rust_type_document typ
    val header =
      keyword "fn" @ space @ identifier name @
      parenthesized
        (comma_documents (map parameter_document parameters)) @
      (case return_type of
         NONE => []
       | SOME typ =>
           space @ delimiter "->" @ space @ rust_type_document typ)
    val body_document =
      (case body of
         UE_Block _ =>
           expression_document options expression_body_precedence body
       | _ => malformed "function item body is not brace-delimited")
  in block 2 false (header @ space @ body_document) end

fun events_of_function options function =
  function_document options function

fun lexical_pretty Keyword_Role text =
      Pretty.mark_str (Markup.keyword1, text)
  | lexical_pretty Operator_Role text =
      Pretty.mark_str (Markup.operator, text)
  | lexical_pretty Delimiter_Role text =
      Pretty.mark_str (Markup.delimiter, text)
  | lexical_pretty Numeral_Role text =
      Pretty.mark_str (Markup.numeral, text)
  | lexical_pretty String_Role text =
      Pretty.mark_str (Markup.inner_string, text)
  | lexical_pretty Identifier_Role text =
      Pretty.str text
  | lexical_pretty Embedded_Role text =
      Pretty.mark_str (Markup.literal, text)

datatype located_token =
  Located_Token of token * (int * int) option

datatype document =
  Document of
    {tokens: token list,
     probe_text: string,
     located_tokens: located_token list}

type lexeme =
  {text: string,
   range: int * int,
   fallback: string -> Pretty.T}

fun finalize_document tokens =
  let
    fun append_text text (offset, fragments) =
      (offset + length (Symbol.explode text), text :: fragments)

    fun add token (offset, fragments, located) =
      (case token of
         Lexeme (_, text) =>
           let
             val start_offset = offset
             val (end_offset, fragments') =
               append_text text (offset, fragments)
           in
             (end_offset, fragments',
              Located_Token
                (token, SOME (start_offset, end_offset)) :: located)
           end
       | Break (width, _) =>
           let
             val (offset', fragments') =
               append_text (Symbol.spaces width) (offset, fragments)
           in
             (offset', fragments',
              Located_Token (token, NONE) :: located)
           end
       | Forced_Break =>
           let
             val (offset', fragments') =
               append_text "\n" (offset, fragments)
           in
             (offset', fragments',
              Located_Token (token, NONE) :: located)
           end
       | Begin_Block _ =>
           (offset, fragments, Located_Token (token, NONE) :: located)
       | End_Block =>
           (offset, fragments, Located_Token (token, NONE) :: located))

    val (_, fragments, located) =
      fold add tokens (1, [], [])
  in
    Document
      {tokens = tokens,
       probe_text = String.concat (rev fragments),
       located_tokens = rev located}
  end

fun document_of_expr options expression =
  finalize_document (events_of_expr options expression)

fun document_of_datatype options item =
  finalize_document (events_of_datatype options item)

fun document_of_function options function =
  finalize_document (events_of_function options function)

fun document_tokens (Document {tokens, ...}) = tokens
fun probe_text (Document {probe_text, ...}) = probe_text

fun render_document render_lexeme
    (Document {located_tokens, ...}) =
  let
    fun parse inside tokens =
      let
        fun finish body rest = (rev body, rest)
        fun loop body [] =
              if inside
              then malformed "unterminated document block"
              else finish body []
          | loop body
              (Located_Token (End_Block, _) :: rest) =
              if inside
              then finish body rest
              else malformed "unexpected document block end"
          | loop body
              (Located_Token
                (Lexeme (role, text), SOME range) :: rest) =
              loop
                (render_lexeme
                  {text = text,
                   range = range,
                   fallback = lexical_pretty role} :: body)
                rest
          | loop _ (Located_Token (Lexeme _, NONE) :: _) =
              malformed "lexeme without generated range"
          | loop body
              (Located_Token (Break (width, indent), _) :: rest) =
              loop (Pretty.brk_indent width indent :: body) rest
          | loop body
              (Located_Token (Forced_Break, _) :: rest) =
              loop (Pretty.fbrk :: body) rest
          | loop body
              (Located_Token
                (Begin_Block (indent, consistent), _) :: rest) =
              let
                val (nested, rest') = parse true rest
                val pretty =
                  Pretty.markup_block
                    {markup = Markup.empty,
                     open_block = false,
                     consistent = consistent,
                     indent = indent}
                    nested
              in loop (pretty :: body) rest' end
      in loop [] tokens end
    val (body, rest) = parse false located_tokens
    val _ =
      if null rest then ()
      else malformed "unconsumed source-mapped document tokens"
  in Pretty.block0 body end

fun default_lexeme
    ({text, fallback, ...}: lexeme) =
  fallback text

fun tokens_of_expr options expression =
  document_tokens (document_of_expr options expression)

fun tokens_of_datatype options item =
  document_tokens (document_of_datatype options item)

fun tokens_of_function options function =
  document_tokens (document_of_function options function)

fun pretty_tokens tokens =
  render_document default_lexeme (finalize_document tokens)

fun pretty_expr options expression =
  render_document default_lexeme
    (document_of_expr options expression)

fun pretty_datatype options item =
  render_document default_lexeme
    (document_of_datatype options item)

fun pretty_function options function =
  render_document default_lexeme
    (document_of_function options function)

fun string_of_expr options =
  pretty_expr options #>
  Pretty.string_of_ops (Pretty.pure_output_ops (SOME 80))

fun string_of_datatype options =
  pretty_datatype options #>
  Pretty.string_of_ops (Pretty.pure_output_ops (SOME 80))

fun string_of_function options =
  pretty_function options #>
  Pretty.string_of_ops (Pretty.pure_output_ops (SOME 80))
end

in

structure URust_Printer :> URUST_PRINTER =
  URust_Printer_Implementation

structure URust_Printer_Document :> URUST_PRINTER_DOCUMENT =
struct
  type document = URust_Printer_Implementation.document
  type lexeme = URust_Printer_Implementation.lexeme

  val human_expr =
    URust_Printer_Implementation.document_of_expr
      URust_Printer_Implementation.human_options
  val human_datatype =
    URust_Printer_Implementation.document_of_datatype
      URust_Printer_Implementation.human_options
  val human_function =
    URust_Printer_Implementation.document_of_function
      URust_Printer_Implementation.human_options
  val probe_text = URust_Printer_Implementation.probe_text
  val pretty = URust_Printer_Implementation.render_document
end

end
\<close>

end
