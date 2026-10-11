theory Parser_Use_Base_Fixtures
  imports Parser_Use_Fixtures
begin

text\<open>
The shared root of the import merge diamond. Its persistent import is inherited by both branches
and must merge idempotently, retaining its declaration identity.
\<close>

urust_use \<open> use demo::increment as shared_increment; \<close>

end
