theory Parser_Use_Left_Fixtures
  imports Parser_Use_Base_Fixtures
begin

text\<open>
One branch of the import merge diamond. It adds a branch-local import and an independent import
whose alias and canonical target agree with the other branch.
\<close>

local_setup \<open>
  URust_Imports.install
    (Parser_Use_Test.item (Parser_Use_Test.leaf ["demo", "value"] (SOME "left_value")))
  #> URust_Imports.install
    (Parser_Use_Test.item (Parser_Use_Test.leaf ["demo", "WIDTH"] (SOME "merged_width")))
\<close>

end
