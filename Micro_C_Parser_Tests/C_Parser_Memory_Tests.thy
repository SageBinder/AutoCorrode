(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Memory_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Lvalues, pointers, aggregates, and initialization\<close>

c_source Memory [addr = nat] \<open>
  struct point { int x; int y; };
  struct buffer { unsigned int data[4]; };
  union bits { unsigned int whole; unsigned char byte; };
  int read(int *p) { return *p; }
  void write(int *p, int x) { *p = x; }
  void swap(int *p, int *q) { int t = *p; *p = *q; *q = t; }
  unsigned int array_read(unsigned int a[], unsigned int i) { return a[i]; }
  void array_write(unsigned int a[], unsigned int i, unsigned int x) { a[i] = x; }
  int field_read(struct point *p) { return p->x; }
  void field_write(struct point *p, int x) { p->x = x; }
  unsigned int array_field(struct buffer *p, unsigned int i) { return p->data[i]; }
  void array_field_write(struct buffer *p, unsigned int i) { p->data[i] += 1; }
  unsigned int array_field_increment(struct buffer *p, unsigned int i) {
    return p->data[i]++;
  }
  void array_field_dot(struct buffer *p, unsigned int i) { (*p).data[i] += 1; }
  unsigned int address_local(void) {
    unsigned int x = 3;
    unsigned int *p = &x;
    *p += 1;
    return x;
  }
  unsigned int address_index(unsigned int *a, unsigned int i) {
    unsigned int *p = &a[i];
    return *p;
  }
  unsigned int parameter_address(unsigned int n) {
    unsigned int *p = &n;
    *p += 1;
    return n;
  }
  void local_array(void) { unsigned int a[4] = {1, 2}; unsigned int x = a[2]; }
  void designated_array(void) {
    unsigned int a[5] = {[1] = 7, [3] = 9};
    unsigned int x = a[1];
  }
  void multidimensional(void) {
    unsigned int a[2][2] = {{1, 2}, {3, 4}};
    unsigned int x = a[1][0];
  }
  void string_array(void) { char a[] = "Hi"; char x = a[0]; }
  void record_literal(struct point *p) { *p = (struct point){1, 2}; }
  unsigned int union_read(union bits *p) { return p->whole; }
  void union_write(union bits *p) { p->whole = 7; }
  unsigned int from_void(void *p) { return *(unsigned int *)p; }
  void *to_void(unsigned int *p) { return (void *)p; }
  static const unsigned int table[3] = {7, 8, 9};
  unsigned int table_read(unsigned int i) { return table[i]; }
\<close>

ML_val \<open>
  val _ = C_Parser_Test.check_definitions \<^context> "Memory"
    ["read", "write", "swap", "array_read", "array_write", "field_read",
     "field_write", "array_field", "array_field_write", "array_field_increment",
     "array_field_dot", "address_local",
     "address_index", "parameter_address", "local_array", "designated_array", "multidimensional",
     "string_array", "record_literal", "union_read", "union_write", "from_void",
     "to_void", "table", "table_read"]
  val _ = List.app (fn name =>
    C_Parser_Test.require_consts \<^context> ("Memory." ^ name)
      [\<^const_name>\<open>store_dereference_const\<close>] [])
    ["read", "swap", "array_read", "field_read"]
  val _ = C_Parser_Test.require_consts \<^context> "Memory.table_read"
    [\<^const_name>\<open>nth\<close>] [\<^const_name>\<open>store_dereference_const\<close>]
  val _ = List.app (fn name =>
    C_Parser_Test.require_consts \<^context> ("Memory." ^ name)
      [\<^const_name>\<open>store_update_const\<close>] [])
    ["write", "swap", "array_write", "field_write"]
  val _ = List.app (fn name =>
    C_Parser_Test.require_consts \<^context> ("Memory." ^ name)
      [\<^const_name>\<open>BufferOverflow\<close>, \<^const_name>\<open>c_abort\<close>] [])
    ["array_read", "array_write", "table_read"]
  val _ = C_Parser_Test.assert "partial initializer lost zero fill"
    (Term.exists_subterm
      (fn t => can HOLogic.dest_list t andalso
        length (HOLogic.dest_list t) = 4 | _ => false)
      (C_Parser_Test.rhs \<^context> "Memory.local_array"))
  val _ = List.app (fn (application, result) =>
    C_Parser_Test.evaluates \<^context> ("Memory.table_read " ^ application) result)
    [("0", "Success 7"), ("2", "Success 9"),
     ("3", "Abort (CustomAbort BufferOverflow)"),
     ("4294967295", "Abort (CustomAbort BufferOverflow)")]
\<close>

end
