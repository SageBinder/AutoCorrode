(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Name_Resolution_Tests
  imports C_Parser_Test_Utils
begin

definition helper :: nat where "helper = 99"
definition zip :: nat where "zip = 88"

c_source NamesLeft \<open>
  static const unsigned int value = 3;
  unsigned int helper(unsigned int x) { return x + value; }
  unsigned int caller(unsigned int zip) { return helper(zip); }
  unsigned int enum_shadow(unsigned int value) { return value; }
\<close>

c_source NamesRight \<open>
  static const unsigned int value = 7;
  unsigned int helper(unsigned int x) { return x + value; }
  unsigned int caller(unsigned int zip) { return helper(zip); }
\<close>

ML_val \<open>
  fun full name = #1 (dest_Const (C_Parser_Test.constant \<^context> name))
  val _ = List.app (fn (unit, foreign) =>
    let
      val _ = C_Parser_Test.check_definitions \<^context> unit
        ["value", "helper", "caller"]
      val _ = C_Parser_Test.require_consts \<^context> (unit ^ ".helper")
        [full (unit ^ ".value")] [full (foreign ^ ".value"), \<^const_name>\<open>helper\<close>]
      val _ = C_Parser_Test.require_consts \<^context> (unit ^ ".caller")
        [full (unit ^ ".helper")]
        [full (foreign ^ ".helper"), \<^const_name>\<open>helper\<close>, \<^const_name>\<open>zip\<close>,
         \<^const_name>\<open>List.zip\<close>]
    in () end)
    [("NamesLeft", "NamesRight"), ("NamesRight", "NamesLeft")]
  val _ = C_Parser_Test.require_consts \<^context> "NamesLeft.enum_shadow"
    [] [full "NamesLeft.value"]
\<close>

end
