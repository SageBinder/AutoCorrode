theory Parser_Use_Left_Fixtures
  imports Parser_Use_Base_Fixtures
begin

text\<open>
One branch of the import merge diamond. It adds a branch-local import and an independent import
whose alias and canonical target agree with the other branch. Its `MergedCollision` alias meets
a same-named generated function from the other branch only in the merged theory.
\<close>

urust_use \<open> use demo::value as left_value; \<close>
urust_use \<open> use demo::WIDTH as merged_width; \<close>
urust_use \<open> use demo::value as MergedCollision; \<close>

end
