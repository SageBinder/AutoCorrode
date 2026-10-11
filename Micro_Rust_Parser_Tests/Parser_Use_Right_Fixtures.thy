theory Parser_Use_Right_Fixtures
  imports Parser_Use_Base_Fixtures
begin

text\<open>
One branch of the import merge diamond. It adds a branch-local import and an independent import
whose alias and canonical target agree with the other branch.
\<close>

urust_use \<open> use demo::value as right_value; \<close>
urust_use \<open> use demo::WIDTH as merged_width; \<close>

end
