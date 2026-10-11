theory Parser_Use_Base_Fixtures
  imports Parser_Use_Fixtures
begin

text\<open>
The shared root of the import merge diamond. Its persistent import is inherited by both branches
and must merge idempotently, retaining its declaration identity.
\<close>

local_setup \<open>
  URust_Imports.install
    (Parser_Use_Test.item (Parser_Use_Test.leaf ["demo", "increment"] (SOME "shared_increment")))
\<close>

end
