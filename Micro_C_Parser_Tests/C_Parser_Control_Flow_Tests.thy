(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Control_Flow_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Branches, loops, switch, and goto\<close>

c_source Control [addr = nat, gv = nat] \<open>
  unsigned int branch(unsigned int a, unsigned int b) {
    if (a > b) return a; else return b;
  }
  unsigned int early_return(unsigned int x) {
    if (x) return 1;
    return 2;
  }
  unsigned int while_loop(unsigned int n) {
    unsigned int i = 0;
    while (i < n) { i += 1; }
    return i;
  }
  unsigned int do_loop(unsigned int n) {
    unsigned int i = 0;
    do { i += 1; } while (i < n);
    return i;
  }
  unsigned int for_loop(unsigned int n) {
    unsigned int sum = 0;
    for (unsigned int i = 0; i < n; ++i) sum += i;
    return sum;
  }
  unsigned int for_break(unsigned int n) {
    unsigned int sum = 0;
    for (unsigned int i = 0; i < n; ++i) {
      if (i == 3) break;
      sum += i;
    }
    return sum;
  }
  unsigned int for_continue(unsigned int n) {
    unsigned int sum = 0;
    for (unsigned int i = 0; i < n; ++i) {
      if (i == 2) continue;
      sum += i;
    }
    return sum;
  }
  unsigned int loop_return(unsigned int n) {
    while (n > 0) { return n; }
    return 0;
  }
  unsigned int nested(unsigned int n) {
    unsigned int sum = 0;
    for (unsigned int i = 0; i < n; ++i)
      for (unsigned int j = 0; j < n; ++j) {
        if (j == 2) break;
        sum += 1;
      }
    return sum;
  }
  unsigned int switch_basic(unsigned int x) {
    switch (x) {
      case 0: return 10;
      case 1: return 20;
      default: return 99;
    }
  }
  unsigned int switch_fallthrough(unsigned int x) {
    unsigned int result = 0;
    switch (x) {
      case 0: result += 1;
      case 1: result += 2; break;
      default: result = 9;
    }
    return result;
  }
  unsigned int switch_no_default(unsigned int x) {
    unsigned int result = 7;
    switch (x) { case 1: result = 8; break; }
    return result;
  }
  unsigned int switch_in_loop(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i) {
      switch (i) { case 1: break; default: result += 1; }
      result += 2;
    }
    return result;
  }
  unsigned int forward_goto(unsigned int x) {
    if (x) goto done;
    return 2;
    done: return 1;
  }
  unsigned int backward_goto(unsigned int n) {
    unsigned int result = 0;
    again: if (result < n) { result += 1; goto again; }
    return result;
  }
\<close>

ML_val \<open>
  val bounded = ["while_loop", "do_loop", "for_break", "for_continue",
    "loop_return", "nested", "backward_goto"]
  val loops = bounded @ ["for_loop", "switch_in_loop"]
  val _ = C_Parser_Test.check_definitions \<^context> "Control"
    (loops @ ["branch", "early_return", "switch_basic", "switch_fallthrough",
      "switch_no_default", "forward_goto"])
  val _ = List.app (fn name =>
    C_Parser_Test.require_consts \<^context> ("Control." ^ name)
      [\<^const_name>\<open>bounded_while\<close>] []) bounded
  val _ = List.app (fn name =>
    C_Parser_Test.assert (name ^ ": loop fuel missing")
      (hd (C_Parser_Test.value_argument_types \<^context> ("Control." ^ name)) =
        HOLogic.natT)) bounded
  val _ = C_Parser_Test.require_consts \<^context> "Control.for_loop"
    [\<^const_name>\<open>raw_for_loop\<close>] [\<^const_name>\<open>bounded_while\<close>]
  val _ = C_Parser_Test.require_arguments \<^context> "Control.for_loop" [\<^typ>\<open>c_uint\<close>]
  val _ = C_Parser_Test.require_consts \<^context> "Control.branch"
    [\<^const_name>\<open>two_armed_conditional\<close>,
     \<^const_name>\<open>return_func\<close>] []
\<close>

end
