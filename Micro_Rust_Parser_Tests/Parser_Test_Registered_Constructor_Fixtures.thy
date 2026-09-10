theory Parser_Test_Registered_Constructor_Fixtures
  imports Parser_Test_Utils
begin

text\<open>
Shared registered-constructor fixtures used by negative conformance and the structural regression
audits. Keeping these declarations neutral avoids making either test suite import the other.
\<close>

datatype negative_registered_constructor_fixture =
    NegativeRegisteredNullary
  | NegativeRegisteredUnary nat
  | NegativeRegisteredOther

datatype 'a negative_registered_phantom =
  NegativeRegisteredPhantom

definition negative_registered_nonconstructor ::
  negative_registered_constructor_fixture where
  \<open>
    negative_registered_nonconstructor \<equiv>
      NegativeRegisteredNullary
  \<close>

definition negative_registered_number :: nat where
  \<open> negative_registered_number \<equiv> 42 \<close>

micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Nullary")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredUnary
  ("NegativeRegistered::Unary")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Other")
micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::Value")
micro_rust_notation (literal)
  negative_registered_number
  ("NegativeRegistered::Number")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Ambiguous")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredOther
  ("NegativeRegistered::Ambiguous")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::ConstructorWins")
micro_rust_notation (literal)
  negative_registered_nonconstructor
  ("NegativeRegistered::ConstructorWins")
micro_rust_notation (literal)
  \<open> NegativeRegisteredUnary 0 \<close>
  ("NegativeRegistered::Applied")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")
micro_rust_notation (literal)
  negative_registered_constructor_fixture.NegativeRegisteredNullary
  ("NegativeRegistered::Duplicate")
micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      nat negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")
micro_rust_notation (literal)
  \<open>
    NegativeRegisteredPhantom ::
      bool negative_registered_phantom
  \<close>
  ("NegativeRegistered::Phantom")

end
