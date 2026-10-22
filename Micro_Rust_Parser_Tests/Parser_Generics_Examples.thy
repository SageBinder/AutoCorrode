(* Readable examples of trait mappings and generic function items.
   The ML audits are in Parser_Generics_ML_Tests. *)

theory Parser_Generics_Examples
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Impl_Trait_Mappings
begin

chapter\<open> Trait mappings \<close>

declare [[urust_verbosity = 0]]

class trait_scale =
  fixes trait_ceiling :: \<open>'a itself \<Rightarrow> nat\<close>

class trait_flag =
  fixes trait_enabled :: \<open>'a itself \<Rightarrow> bool\<close>

instantiation nat :: trait_scale
begin

definition trait_ceiling_nat :: \<open>nat itself \<Rightarrow> nat\<close> where
  \<open>trait_ceiling_nat _ = 12\<close>

instance ..

end

urust_trait "Scale" = \<open> trait_scale \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>

urust_trait "Marker" = \<open> type \<close>

urust_trait "RedundantScale" = \<open> {trait_scale, type} \<close>
  urust_consts "HEIGHT" = \<open> trait_ceiling \<close>

urust_trait "demo::ScaleFlag" = \<open> {trait_scale, trait_flag} \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>
    and "ENABLED" = \<open> trait_enabled \<close>

text\<open> An identical declaration is accepted and retains the original mapping. \<close>

urust_trait "Scale" = \<open> trait_scale \<close>
  urust_consts "CEILING" = \<open> trait_ceiling \<close>

urust_trait "SlotOne" = \<open> type \<close>
  urust_consts "SLOT" = \<open> \<lambda>(_ :: 'a itself). (3 :: nat) \<close>

urust_trait "SlotTwo" = \<open> type \<close>
  urust_consts "SLOT" = \<open> \<lambda>(_ :: 'a itself). (4 :: nat) \<close>

locale trait_offset =
  fixes offset :: nat
begin

definition offset_ceiling :: \<open>'a itself \<Rightarrow> nat\<close> where
  \<open>offset_ceiling _ = offset\<close>

urust_trait "OffsetScale" = \<open> type \<close>
  urust_consts "OFFSET" = \<open> offset_ceiling \<close>

end

interpretation seven_offset: trait_offset 7 .

lemma interpreted_offset_ceiling:
  \<open>seven_offset.offset_ceiling TYPE(bool) = 7\<close>
  unfolding trait_offset.offset_ceiling_def by (rule refl)

text\<open>
The registry is available independently of generic function syntax. Function bounds and
associated-constant expressions consume it in the later units.
\<close>

chapter\<open> Syntax \<close>

text\<open> Reserved for U2 generic syntax examples. \<close>

chapter\<open> Signatures \<close>

text\<open> Reserved for U3 generic signature examples. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body examples. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call examples. \<close>

end
