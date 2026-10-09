(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Runtime_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Executable reference fixture\<close>

text \<open>
  A small deterministic store makes mutation and control flow observable.
  References carry the production focus type; reading and writing respect that
  focus. This fixture is for scalar execution tests, and does not model byte
  layout or allocation lifetime. Those contracts are checked in the C examples.
\<close>

type_synonym test_ref = "(nat, c_uint, c_uint) State_References.ref"

definition heap_ref :: "nat \<Rightarrow> test_ref" where
  "heap_ref n = make_focused (make_gref n) focus_id"

definition heap_new ::
    "c_uint \<Rightarrow> (c_uint list, test_ref, c_abort, 'i, 'o) function_body" where
  "heap_new value = FunctionBody (Expression (\<lambda>cells.
    Success (heap_ref (length cells)) (cells @ [value])))"

definition heap_read ::
    "test_ref \<Rightarrow> (c_uint list, c_uint, c_abort, 'i, 'o) function_body" where
  "heap_read r = FunctionBody (Expression (\<lambda>cells.
    if ref_address r < length cells then
      case focus_view (get_focus r) (cells ! ref_address r) of
        Some value \<Rightarrow> Success value cells
      | None \<Rightarrow> Abort TypeError cells
    else Abort DanglingPointer cells))"

definition heap_write ::
    "test_ref \<Rightarrow> c_uint \<Rightarrow>
      (c_uint list, unit, c_abort, 'i, 'o) function_body" where
  "heap_write r value = FunctionBody (Expression (\<lambda>cells.
    if ref_address r < length cells then
      Success () (cells[ref_address r :=
        focus_update (get_focus r) value (cells ! ref_address r)])
    else Abort DanglingPointer cells))"

adhoc_overloading store_reference_const \<rightleftharpoons> heap_new
adhoc_overloading store_dereference_const \<rightleftharpoons> heap_read
adhoc_overloading store_update_const \<rightleftharpoons> heap_write

lemmas heap_test_simps =
  heap_ref_def heap_new_def heap_read_def heap_write_def focus_id_components

section \<open>Stateful C programs\<close>

c_source Runtime [addr = nat, gv = c_uint] \<open>
  unsigned int local(unsigned int n) { unsigned int x = n; x += 2; return x; }
  unsigned int parameter(unsigned int n) { n += 2; return n; }
  unsigned int parameter_address(unsigned int n) {
    unsigned int *p = &n;
    *p += 1;
    return n;
  }
  unsigned int scope(unsigned int n) {
    unsigned int result = n;
    { unsigned int n = 9; result += n; }
    return result;
  }
  unsigned int pre_increment(void) { unsigned int x = 4; return ++x; }
  unsigned int post_increment(void) { unsigned int x = 4; return x++; }
  unsigned int pre_decrement(void) { unsigned int x = 4; return --x; }
  unsigned int post_decrement(void) { unsigned int x = 4; return x--; }
  unsigned int chained_assignment(void) {
    unsigned int x = 0, y = 0;
    x = y = 7;
    return x + y;
  }
  unsigned int comma_assignment(void) {
    unsigned int x = 0;
    return (x = 3, x += 4, x);
  }
  unsigned int compound(void) {
    unsigned int x = 20;
    x += 4; x -= 2; x *= 3; x /= 2; x %= 16;
    x |= 16; x &= 31; x ^= 3; x <<= 1; x >>= 2;
    return x;
  }
  unsigned int while_loop(unsigned int n) {
    unsigned int x = 0;
    while (x < n) ++x;
    return x;
  }
  unsigned int do_loop(unsigned int n) {
    unsigned int x = 0;
    do { ++x; } while (x < n);
    return x;
  }
  unsigned int for_loop(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i) result += i;
    return result;
  }
  unsigned int break_loop(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i) {
      if (i == 3) break;
      result += i;
    }
    return result;
  }
  unsigned int continue_loop(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i) {
      if (i == 2) continue;
      result += i;
    }
    return result;
  }
  unsigned int loop_return(unsigned int n) {
    while (n > 0) { return n; }
    return 0;
  }
  unsigned int nested(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i)
      for (unsigned int j = 0; j < n; ++j) {
        if (j == 2) break;
        ++result;
      }
    return result;
  }
  unsigned int switch_in_loop(unsigned int n) {
    unsigned int result = 0;
    for (unsigned int i = 0; i < n; ++i) {
      switch (i) { case 1: break; default: ++result; }
      result += 2;
    }
    return result;
  }
  unsigned int switch_fallthrough(unsigned int n) {
    unsigned int result = 0;
    switch (n) {
      case 0: result += 1;
      case 1: result += 2; break;
      default: result = 9;
    }
    return result;
  }
  unsigned int switch_return(unsigned int n) {
    switch (n) { case 0: return 10; default: return 20; }
  }
  unsigned int forward_goto(unsigned int n) {
    unsigned int result = 1;
    if (n) goto done;
    result = 2;
    done: return result;
  }
  unsigned int backward_goto(unsigned int n) {
    unsigned int result = 0;
    again: if (result < n) { ++result; goto again; }
    return result;
  }
  unsigned int read(unsigned int *p) { return *p; }
  void write(unsigned int *p, unsigned int value) { *p = value; }
  void swap(unsigned int *p, unsigned int *q) {
    unsigned int t = *p;
    *p = *q;
    *q = t;
  }
\<close>

ML_val \<open>
local
  val ctxt = \<^context>
  val _ = C_Parser_Test.check_definitions ctxt "Runtime"
    ["local", "parameter", "parameter_address", "scope", "pre_increment", "post_increment",
     "pre_decrement", "post_decrement", "chained_assignment", "comma_assignment",
     "compound", "while_loop", "do_loop", "for_loop", "break_loop",
     "continue_loop", "loop_return", "nested", "switch_in_loop",
     "switch_fallthrough", "switch_return", "forward_goto", "backward_goto",
     "read", "write", "swap"]
  val facts = ["shallow_computation_simps", "c_test_eval_simps", "heap_test_simps"]
  fun result application expected =
    C_Parser_Test.prove ctxt facts
      ("(case evaluate (call (" ^
       C_Parser_Test.c_application ctxt ("Runtime." ^ application) ^ ")) [] of " ^
       "Success value cells => value = " ^ expected ^ " | _ => False)")
  (* Fuel is intentionally explicit: zero and insufficient fuel test the
     bounded semantics as well as the enough-fuel cases. *)
  val rows =
    [("local 5", "7"), ("parameter 5", "7"), ("parameter_address 5", "6"), ("scope 5", "14"),
     ("pre_increment", "5"), ("post_increment", "4"),
     ("pre_decrement", "3"), ("post_decrement", "4"),
     ("chained_assignment", "14"), ("comma_assignment", "7"), ("compound", "9"),
     ("while_loop 0 5", "0"), ("while_loop 2 5", "2"), ("while_loop 6 5", "5"),
     ("do_loop 6 0", "1"), ("do_loop 6 4", "4"),
     ("for_loop 0", "0"), ("for_loop 5", "10"),
     ("break_loop 8 7", "3"), ("continue_loop 8 5", "8"),
     ("loop_return 0 5", "0"), ("loop_return 1 5", "5"),
     ("nested 6 3", "6"), ("switch_in_loop 4", "11"),
     ("switch_fallthrough 0", "3"), ("switch_fallthrough 1", "2"),
     ("switch_fallthrough 9", "9"),
     ("switch_return 0", "10"), ("switch_return 9", "20"),
     ("forward_goto 0", "2"), ("forward_goto 1", "1"),
     ("backward_goto 6 3", "3")]
  val _ = List.app (fn (application, expected) => result application expected) rows
  (* With no backward-goto fuel, execution never reaches the C return.
     Check the untouched result cell, without assigning a value to fall-through. *)
  val _ = C_Parser_Test.prove ctxt facts
    ("(case evaluate (call (" ^
     C_Parser_Test.c_application ctxt "Runtime.backward_goto 0 3" ^ ")) [] of " ^
     "Success value cells => drop 1 cells = [0] | _ => False)")
  val _ = C_Parser_Test.prove ctxt facts
    "evaluate (call (Runtime.read (heap_ref 0))) [11, 22] = Success 11 [11, 22]"
  val _ = C_Parser_Test.prove ctxt facts
    "evaluate (call (Runtime.write (heap_ref 1) 7)) [11, 22] = Success () [11, 7]"
  val _ = C_Parser_Test.prove ctxt facts
    "evaluate (call (Runtime.read (heap_ref 2))) [11, 22] = Abort DanglingPointer [11, 22]"
  val _ = C_Parser_Test.prove ctxt facts
    "evaluate (call (Runtime.write (heap_ref 2) 7)) [11, 22] = Abort DanglingPointer [11, 22]"
  val _ = C_Parser_Test.prove ctxt facts
    "(case evaluate (call (Runtime.swap (heap_ref 0) (heap_ref 1))) [11, 22] of \
    \Success value cells => value = () & take 2 cells = [22, 11] | _ => False)"
in
  val _ = ()
end
\<close>

end
