theory C_File_Load_Smoke
  imports
    C_To_Core_Translation
begin

section \<open>c_file Smoke Test\<close>

c_file "C" "smoke_test_file.c"

thm C.file_add_def

end
