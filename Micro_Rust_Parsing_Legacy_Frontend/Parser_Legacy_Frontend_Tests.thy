(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Legacy_Frontend_Tests
  imports
    Micro_Rust_Shallow_Embedding
begin

section\<open>Parsing and Evaluation Tests for the Shallow Embedding\<close>

text\<open>Comprehensive test coverage for the Micro Rust shallow embedding.
This file contains tests organized by language feature category.\<close>

subsection\<open>Literals and Basic Values\<close>

subsubsection\<open>Numeric Literals\<close>

term\<open>\<lbrakk> 0 \<rbrakk>\<close>
term\<open>\<lbrakk> 1 \<rbrakk>\<close>
term\<open>\<lbrakk> 42 \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>1 :: 64 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>255 :: 8 word\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Boolean Literals\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>Bool_Type.true\<close>
\<rbrakk>\<close>

term\<open>\<lbrakk> True \<rbrakk>\<close>
term\<open>\<lbrakk> False \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>False\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Unit Literal\<close>

context
  fixes f :: \<open>unit \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>unit \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> () \<rbrakk>\<close>
term \<open>\<lbrakk> (); () \<rbrakk>\<close>
term \<open>\<lbrakk> (); (); \<rbrakk>\<close>
term \<open>\<lbrakk> return (); \<rbrakk>\<close>
term \<open>\<lbrakk> return; \<rbrakk>\<close>
term \<open>\<lbrakk> f(()) \<rbrakk>\<close>
term \<open>\<lbrakk> g((),True) \<rbrakk>\<close>
end

subsubsection\<open>String Literals\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
term \<open>\<lbrakk> panic!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> panic!( \<llangle>''oh no!''\<rrangle> ) \<rbrakk>\<close>
end

subsubsection\<open>HOL Value Injection (Antiquotation)\<close>

term\<open>\<lbrakk> \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>True\<rrangle> \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>

subsection\<open>Type Casts and Ascriptions\<close>

subsubsection\<open>Type Casting\<close>

context
  fixes a_value :: \<open>32 word\<close>
begin
term\<open>\<lbrakk> a_value as u8\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u32\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as u64; a_value as u64\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as usize\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as i32\<rbrakk>\<close>
term\<open>\<lbrakk> a_value as i64\<rbrakk>\<close>
end

subsubsection\<open>Raw Pointer Casts\<close>

context
  fixes raw_buf :: \<open>('addr, 'gv) gref\<close>
begin
term\<open>\<lbrakk> raw_buf as *const u8 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *const u16 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *const u32 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *const u64 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *const usize \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *mut u8 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *mut u32 \<rbrakk>\<close>
term\<open>\<lbrakk> raw_buf as *mut u64 \<rbrakk>\<close>
end

subsubsection\<open>Numeric Ascriptions\<close>

term \<open>\<lbrakk> 0_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x4_u8 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x12_u16 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2000_u32 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 1_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0x2f0_u64 \<rbrakk>\<close>
term \<open>\<lbrakk> 0_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 1_usize \<rbrakk>\<close>
term \<open>\<lbrakk> 0xffffffff0_usize \<rbrakk>\<close>

subsection\<open>Boolean Operators\<close>

subsubsection\<open>Boolean Negation\<close>

term\<open>\<lbrakk> !True \<rbrakk>\<close>
term\<open>\<lbrakk> !False \<rbrakk>\<close>
term\<open>\<lbrakk> !!True \<rbrakk>\<close>

term\<open>\<lbrakk>
  if !True {
    return;
  }
\<rbrakk>\<close>

subsubsection\<open>Boolean Conjunction\<close>

term\<open>\<lbrakk> True && True \<rbrakk>\<close>
term\<open>\<lbrakk> True && False \<rbrakk>\<close>
term\<open>\<lbrakk> False && True \<rbrakk>\<close>
term\<open>\<lbrakk> False && False \<rbrakk>\<close>

subsubsection\<open>Boolean Disjunction\<close>

term\<open>\<lbrakk> True || True \<rbrakk>\<close>
term\<open>\<lbrakk> True || False \<rbrakk>\<close>
term\<open>\<lbrakk> False || True \<rbrakk>\<close>
term\<open>\<lbrakk> False || False \<rbrakk>\<close>

term\<open>\<lbrakk>
  if (\<llangle>True\<rrangle> || \<llangle>True\<rrangle> && \<llangle>False\<rrangle>) {
    \<epsilon>\<open>\<up>0\<close>
  } else {
    \<epsilon>\<open>\<up>0\<close>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True || !True {
    {{{{{{{{{{
      42
    }}}}}}}}}}
  } else {
    0
  }
\<rbrakk>\<close>

subsection\<open>Comparison Operators\<close>

subsubsection\<open>Equality and Nonequality\<close>

context
  fixes m n :: \<open>nat\<close>
  fixes h :: \<open>nat \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes x y :: \<open>64 word\<close>
begin
term \<open>\<lbrakk> m == n \<rbrakk>\<close>
term \<open>\<lbrakk> !(m == n) \<rbrakk>\<close>
term \<open>\<lbrakk> m != n \<rbrakk>\<close>
term \<open>\<lbrakk> m.h() \<rbrakk>\<close>
term \<open>\<lbrakk> if m.h() == n { m } else { n } \<rbrakk>\<close>
end

subsubsection\<open>Ordering Comparisons\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x < y \<rbrakk>\<close>
term \<open>\<lbrakk> x <= y \<rbrakk>\<close>
term \<open>\<lbrakk> x > y \<rbrakk>\<close>
term \<open>\<lbrakk> x >= y \<rbrakk>\<close>
term \<open>\<lbrakk> x > \<llangle>0 :: 32 word\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Arithmetic Operators\<close>

subsubsection\<open>Addition\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  a + b
\<rbrakk>\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
term\<open>\<lbrakk>
  let (a,b,c) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>, \<llangle>3 :: 64 word\<rrangle>);
  a + b + c
\<rbrakk>\<close>
end

subsubsection\<open>Subtraction\<close>

term\<open>\<lbrakk>
  let a = \<llangle>5 :: 32 word\<rrangle>;
  let b = \<llangle>3 :: 32 word\<rrangle>;
  a - b
\<rbrakk>\<close>

subsubsection\<open>Multiplication\<close>

term\<open>\<lbrakk>
  let a = \<llangle>3 :: 32 word\<rrangle>;
  let b = \<llangle>4 :: 32 word\<rrangle>;
  a * b
\<rbrakk>\<close>

subsubsection\<open>Division\<close>

term\<open>\<lbrakk>
  let a = \<llangle>12 :: 32 word\<rrangle>;
  let b = \<llangle>4 :: 32 word\<rrangle>;
  a / b
\<rbrakk>\<close>

subsubsection\<open>Modulo\<close>

term\<open>\<lbrakk>
  let a = \<llangle>17 :: 32 word\<rrangle>;
  let b = \<llangle>5 :: 32 word\<rrangle>;
  a % b
\<rbrakk>\<close>

subsection\<open>Bitwise Operators\<close>

subsubsection\<open>Bitwise AND\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0xFF :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a & b
\<rbrakk>\<close>

subsubsection\<open>Bitwise OR\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0xF0 :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a | b
\<rbrakk>\<close>

subsubsection\<open>Bitwise XOR\<close>

context
  fixes x y :: \<open>64 word\<close>
begin
term \<open>\<lbrakk> !x + y \<rbrakk>\<close>
term \<open>\<lbrakk> !(!x == x^y)  \<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let a = \<llangle>0xFF :: 32 word\<rrangle>;
  let b = \<llangle>0x0F :: 32 word\<rrangle>;
  a ^ b
\<rbrakk>\<close>

subsubsection\<open>Bitwise NOT (Word Negation)\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0x00 :: 8 word\<rrangle>;
  !a
\<rbrakk>\<close>

subsubsection\<open>Left Shift\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  a << \<llangle>4 :: 64 word\<rrangle>
\<rbrakk>\<close>

subsubsection\<open>Right Shift\<close>

term\<open>\<lbrakk>
  let a = \<llangle>16 :: 32 word\<rrangle>;
  a >> \<llangle>2 :: 64 word\<rrangle>
\<rbrakk>\<close>

subsection\<open>Assignment Operators\<close>

subsubsection\<open>Simple Assignment\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
begin

private definition dummy_dereference_assign :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_assign \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_assign

term \<open>\<lbrakk> r = 10 \<rbrakk>\<close>
term \<open>\<lbrakk> r = *r \<rbrakk>\<close>
term \<open>\<lbrakk> (r) = *r \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_assign
end

subsubsection\<open>Place Assignment Forms\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  (*x) = b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Add-Assign\<close>

context
  fixes a b :: \<open>'s\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x += b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Subtract-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x -= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Multiply-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x *= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Modulo-Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x %= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Bitwise Assign\<close>

context
  fixes a b :: \<open>32 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x |= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x &= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x ^= b;
  *x
\<rbrakk>\<close>
end

subsubsection\<open>Shift-Assign\<close>

context
  fixes a :: \<open>32 word\<close>
  fixes b :: \<open>64 word\<close>
begin
term \<open>\<lbrakk>
  let mut x = a;
  x <<= b;
  *x
\<rbrakk>\<close>

term \<open>\<lbrakk>
  let mut x = a;
  x >>= b;
  *x
\<rbrakk>\<close>
end

subsection\<open>Control Flow - Conditionals\<close>

subsubsection\<open>Two-Armed Conditionals\<close>

term\<open>\<lbrakk>
  if True {
    return True;
  } else {
    return True;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if \<llangle>True\<rrangle> {
    let v = 16;
    return v;
  } else {
    42
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), if False { (2 as u32, 3 as u32) } else { (4, 5) })
\<rbrakk>\<close>

subsubsection\<open>Else-If Conditionals\<close>

term\<open>\<lbrakk>
  if False {
    \<llangle>0 :: 32 word\<rrangle>
  } else if True {
    \<llangle>1 :: 32 word\<rrangle>
  } else {
    \<llangle>2 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if False {
    \<llangle>0 :: 32 word\<rrangle>
  } else if False {
    \<llangle>1 :: 32 word\<rrangle>
  } else if True {
    \<llangle>2 :: 32 word\<rrangle>
  } else {
    \<llangle>3 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  assert!((if False { False } else if True { True } else { False }))
\<rbrakk>\<close>

subsubsection\<open>One-Armed Conditionals\<close>

term\<open>\<lbrakk>
  if True {
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return;
  }
\<rbrakk>\<close>

subsubsection\<open>Nested Conditionals\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    if True {
      return;
    } else {
      return;
    }
  } else {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  ((if True { 0 } else { 1 }, True), False)
\<rbrakk>\<close>

subsubsection\<open>Rust-Style Optional Semicolons for Block-Like Statements\<close>

term\<open>\<lbrakk>
  if True {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if True {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if False {
    ()
  } else if True {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  } else {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(()) {
    Some(_) \<Rightarrow> (),
    _ \<Rightarrow> ()
  }
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # []\<rrangle>;
  for (a, b) in lst {
    ()
  }
  ()
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  { () }
  ()
\<rbrakk>)\<close>

term\<open>\<lbrakk>
  unsafe { () }
  ()
\<rbrakk>\<close>

subsection\<open>Control Flow - If-Let and Let-Else\<close>

subsubsection\<open>If-Let with Option\<close>

term\<open>\<lbrakk>
  if let Some(_) = Some(()) {
    ()
  };
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(()) {
    return;
  } else {
    return;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) {
    assert!(a == \<llangle>1 :: 32 word\<rrangle>);
    assert!(b == \<llangle>2 :: 32 word\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Some(Some(x)) = Some(Some(\<llangle>3 :: 32 word\<rrangle>)) {
    assert!(x == \<llangle>3 :: 32 word\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>If-Let-Else\<close>

term\<open>\<lbrakk>
  if let Some(p) = Some(g) {
    return 0;
  } else {
    return 2;
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Option\<close>

term\<open>\<lbrakk>
  let (a, b) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) else {
    ()
  };
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Some((a, b)) = Some((\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>)) else {
    ()
  };
  assert!(a == \<llangle>1 :: 32 word\<rrangle>);
  assert!(b == \<llangle>2 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  let x = \<llangle>Some (0 :: nat)\<rrangle>;
  let Some(foo) = x else {
    assert!(False)
  };
  return;
\<rbrakk>)\<close>

context
  fixes n :: \<open>nat option\<close>
begin
term \<open>\<lbrakk> let Some(x) = n else { return \<llangle>5\<rrangle>; }; return x; \<rbrakk>\<close>
end

subsubsection\<open>Let-Else with Result\<close>

term\<open>\<lbrakk>
  let Ok(k) = Ok(()) else {
    return;
  };

  return k;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Err(e) = Ok(()) else {
    return True;
  };

  return e;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>7 :: 32 word\<rrangle>;
  let b = \<llangle>9 :: 32 word\<rrangle>;
  let Ok((x, y)) = Ok((a, b)) else {
    ()
  };
  assert!(x == a);
  assert!(y == b)
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Tuples\<close>

term\<open>\<lbrakk>
  let (a,_) = (1,2);
  let (_,b) = (1,2);
  \<llangle>(a,b)\<rrangle>
\<rbrakk>\<close>

subsection\<open>Control Flow - Match Expressions\<close>

subsubsection\<open>Basic Match on Option\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) \<Rightarrow> { return; },
    None \<Rightarrow> { return; }
  };
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
   None \<Rightarrow> { return; },
   Some(y) \<Rightarrow> y
  };
\<rbrakk>\<close>

subsubsection\<open>Match on Result\<close>

term\<open>\<lbrakk>
  let v = match Err(\<llangle>5 :: 32 word\<rrangle>) {
    Ok(_) \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>,
    Err(x) \<Rightarrow> x
  };
  assert!(v == \<llangle>5 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Wildcard Patterns\<close>

term\<open>\<lbrakk>
  let _ = 3;
  let _ = (if True { False} else {True});
  const _ = {
    assert!(True);
    assert!(False);
  };
  let _ = assert!(let _ = False; if let Some(_) = None { False} else {True});
  match Some(a) {
    Some(_) \<Rightarrow> (),
    _ \<Rightarrow> ()
  };
  if let Some(_) = Some(()) {
    ()
  };
  ()
\<rbrakk>\<close>

subsubsection\<open>Variable Binding in Patterns\<close>

term\<open>\<lbrakk>
  let two = \<llangle>2 :: 32 word\<rrangle>;
  let res = match Some(Some(two)) {
    Some(Some(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == two)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = \<llangle>9 :: 32 word\<rrangle>;
  let y = match x {
    z \<Rightarrow> z
  };
  assert!(y == x)
\<rbrakk>\<close>

subsubsection\<open>Grouped and Irrefutable Patterns\<close>

term\<open>\<lbrakk>
  let v = match Some(\<llangle>5 :: 32 word\<rrangle>) {
    (Some(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(v == \<llangle>5 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let foo = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>);
  let (x, y) = foo;
  assert!(x == \<llangle>1 :: 32 word\<rrangle>);
  assert!(y == \<llangle>2 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = \<llangle>7 :: 32 word\<rrangle>;
  if let Some(y) = Some(x) {
    assert!(y == x);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let foo = (\<llangle>3 :: 32 word\<rrangle>, \<llangle>4 :: 32 word\<rrangle>);
  let (x, y) = foo else {
    ()
  };
  assert!(x == \<llangle>3 :: 32 word\<rrangle>);
  assert!(y == \<llangle>4 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Slice Patterns\<close>

term\<open>\<lbrakk>
  let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>;
  let res = match xs {
    [a, b, c] \<Rightarrow> a + b + c,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>6 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>;
  let tag = match xs {
    [_, _] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(tag == \<llangle>0 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let ys = \<llangle>([] :: 32 word list)\<rrangle>;
  let tag = match ys {
    [] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(tag == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let [a, b] = \<llangle>[7 :: 32 word, 8]\<rrangle> {
    assert!(a == \<llangle>7 :: 32 word\<rrangle>);
    assert!(b == \<llangle>8 :: 32 word\<rrangle>);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Extended Rust-Style Pattern Forms\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>True\<rrangle> {
    true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    false \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>String.implode ''ok''\<rrangle> {
    "ok" \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>CHR ''a''\<rrangle> {
    \<llangle>CHR ''a''\<rrangle> \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    whole @ Some(v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

text\<open>Note: Rust-style pattern binders @{text "ref p"} and @{text "ref mut p"} are currently
not supported in this frontend, because they conflict with existing syntax around references
and function parameters in this Isabelle embedding.\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    Some(&v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: 32 word\<rrangle>) {
    Some(& mut v) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

text\<open>Range patterns are lowered in the shallow embedding, but concrete parser-level
coverage for the Rust-style syntax is exercised separately in frontend-focused tests.\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: nat\<rrangle>) {
    Some(5..=7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  };
  assert!(y == \<llangle>1 :: nat\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(\<llangle>7 :: nat\<rrangle>) {
    Some(5..7) \<Rightarrow> \<llangle>1 :: nat\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  };
  assert!(y == \<llangle>0 :: nat\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>[7 :: 32 word, 8, 9]\<rrangle> {
    [head, ..] \<Rightarrow> head,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>[1 :: 32 word, 2, 3, 4]\<rrangle> {
    [a, b, .., y, z] \<Rightarrow> y + z,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> {
    [a, b, .., y, z] \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>0 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match \<llangle>[1 :: 32 word, 2, 3]\<rrangle> {
    [.., y, z] \<Rightarrow> y + z,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>5 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(Some(True)) {
    Some(Some(True)) \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let y = match Some(Some(\<llangle>7 :: 32 word\<rrangle>)) {
    Some(whole @ Some(v)) \<Rightarrow> v,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(y == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Nested Patterns\<close>

term\<open>\<lbrakk>
  let one = \<llangle>1 :: 32 word\<rrangle>;
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  assert!((match Some(Some(None)) {
    Some(None) \<Rightarrow> one,
    _ \<Rightarrow> zero
  }) == zero)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let res = match ((a, b), c) {
    ((x, y), z) \<Rightarrow> (x, y, z)
  };
  assert!(res.0 == a);
  assert!(res.1 == b);
  assert!(res.2 == c)
\<rbrakk>\<close>

subsubsection\<open>Tuple Patterns in Match\<close>

datatype struct_pattern_fixture = Foo (foo: "32 word") (goo: "32 word") | Other

datatype_record struct_pattern_dr =
  dr_foo :: "32 word"
  dr_goo :: "32 word"

record struct_pattern_rec =
  rec_foo :: "32 word"
  rec_goo :: "32 word"

definition foo_struct_expr_lift where
  "foo_struct_expr_lift \<equiv> lift_fun2 Foo"

micro_rust_notation (call) foo_struct_expr_lift ("Foo")

definition struct_pattern_dr_struct_expr_lift where
  "struct_pattern_dr_struct_expr_lift \<equiv> lift_fun2 make_struct_pattern_dr"

micro_rust_notation (call) struct_pattern_dr_struct_expr_lift ("struct_pattern_dr")

term\<open>\<lbrakk>
  match (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>) {
    (a, b) \<Rightarrow> a
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let res = match Some((a, b, c)) {
    Some((x, _, z)) \<Rightarrow> (x, z),
    _ \<Rightarrow> (\<llangle>0 :: 32 word\<rrangle>, \<llangle>0 :: 32 word\<rrangle>)
  };
  assert!(res.0 == a);
  assert!(res.1 == c)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>4 :: 32 word\<rrangle>;
  let b = \<llangle>8 :: 32 word\<rrangle>;
  if let Some((_, y)) = Some((a, b)) {
    assert!(y == b);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>1 :: 32 word\<rrangle>;
  let b = \<llangle>2 :: 32 word\<rrangle>;
  let c = \<llangle>3 :: 32 word\<rrangle>;
  let d = \<llangle>4 :: 32 word\<rrangle>;
  let res = match ((a, b), (c, d)) {
    ((w, x), (y, z)) \<Rightarrow> (w, x, y, z)
  };
  assert!(res.0 == a);
  assert!(res.1 == b);
  assert!(res.2 == c);
  assert!(res.3 == d)
\<rbrakk>\<close>

subsubsection\<open>Struct Patterns\<close>

term\<open>\<lbrakk>
  match \<llangle>Foo (1 :: 32 word) 2\<rrangle> {
    Foo { foo: p, goo: q } \<Rightarrow> p + q,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (3 :: 32 word) 4\<rrangle> {
    Foo { foo: p, goo: q } \<Rightarrow> p + q,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>7 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let Foo { foo: p, goo: q } = \<llangle>Foo (5 :: 32 word) 6\<rrangle> {
    assert!(p == \<llangle>5 :: 32 word\<rrangle>);
    assert!(q == \<llangle>6 :: 32 word\<rrangle>);
    ()
  } else {
    assert!(False);
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let Foo { foo: p, goo: q } = \<llangle>Foo (8 :: 32 word) 9\<rrangle> else {
    return;
  };
  p + q
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>make_struct_pattern_dr (10 :: 32 word) 11\<rrangle> {
    struct_pattern_dr { dr_goo: q, dr_foo: p } \<Rightarrow> p + q
  };
  assert!(res == \<llangle>21 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> {
    Foo { foo, goo } \<Rightarrow> foo + goo,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>46 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let res = match \<llangle>Foo (12 :: 32 word) 34\<rrangle> {
    Foo { foo, .. } \<Rightarrow> foo,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(res == \<llangle>12 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Struct Expressions\<close>

term\<open>\<lbrakk>
  Foo { foo: \<llangle>1 :: 32 word\<rrangle>, goo: \<llangle>2 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  Foo { goo: \<llangle>2 :: 32 word\<rrangle>, foo: \<llangle>1 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  struct_pattern_dr { dr_goo: \<llangle>11 :: 32 word\<rrangle>, dr_foo: \<llangle>10 :: 32 word\<rrangle> }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  Foo { foo: \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, goo: \<llangle>4 :: 32 word\<rrangle> / \<llangle>2 :: 32 word\<rrangle> }
\<rbrakk>\<close>

subsubsection\<open>Pattern Guards\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) if (if True { True } else { False }) \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  let one = \<llangle>1 :: 32 word\<rrangle>;
  let res = match Some(one) {
    Some(x) if x > zero \<Rightarrow> x,
    _ \<Rightarrow> zero
  };
  assert!(res == one)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let zero = \<llangle>0 :: 32 word\<rrangle>;
  let res = match Some(zero) {
    Some(x) if x > zero \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
    Some(x) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
  };
  assert!(res == zero)
\<rbrakk>\<close>

subsubsection\<open>Match with Return\<close>

term\<open>\<lbrakk>
  match Some(x) {
    Some(y) \<Rightarrow> { return; },
    None \<Rightarrow> { return; }
  };
\<rbrakk>\<close>

subsubsection\<open>Numeric Match (\<^verbatim>\<open>match_switch\<close>)\<close>

text\<open>See Section 21 (Rust Path Expressions) for \<^verbatim>\<open>match_switch\<close> examples\<close>

subsection\<open>Control Flow - Loops\<close>

subsubsection\<open>Basic For Loop\<close>

term\<open>\<lbrakk>
  let lst = \<llangle>(1 :: 32 word, 2 :: 32 word, TNil) # (3, 4, TNil) # []\<rrangle>;
  for (a, b) in lst {
    let _ = a;
    let _ = b;
    ()
  };
  ()
\<rbrakk>\<close>

subsubsection\<open>For Loop with Tuple Destructuring\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, ()), ()) # (1, 2, (True, False, ()), ()) # []\<rrangle>;
  for i in lst {
    if (i.2.0) && i.2.1 {
      *x = i.0;
    } else {
      *x = i.1;
    }
  };
  x
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let lst = \<llangle>(1, 2, (True, False, nil), nil) # (1, 2, (True, False, nil), nil) # []\<rrangle>;
  for (a, b, (c, d)) in lst {
    if c && d {
      x += a;
    } else {
      x += b;
    }
  };
  x
\<rbrakk>\<close>

subsubsection\<open>For Loop with Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> for i in x .. y { () } \<rbrakk>\<close>
end

subsubsection\<open>While Loop\<close>

context
  fixes n :: nat
begin
term \<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  #[fuel(\<epsilon>\<open>n\<close>) ] while (*x < 10_u32) {
    x += 1_u32;
  };
  *x
\<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  #[fuel(\<epsilon>\<open>n :: nat\<close>) ] while (*x < 10_u32) {
    x += 1_u32;
  }
  *x
\<rbrakk>\<close>

subsubsection\<open>Loop\<close>

context
  fixes n :: nat
begin
term \<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  #[fuel(\<epsilon>\<open>n\<close>) ] loop {
    x += 1_u32;
  };
  *x
\<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  #[fuel(\<epsilon>\<open>n :: nat\<close>) ] loop {
    x += 1_u32;
  }
  *x
\<rbrakk>\<close>


subsubsection\<open>While Let\<close>

context
  fixes n :: nat
begin

\<comment>\<open>Some pattern with semicolon\<close>
term \<open>\<lbrakk>
  #[fuel(\<epsilon>\<open>n\<close>)]
  while let Some(v) = Some(g) {
    ()
  };
  ()
\<rbrakk>\<close>

\<comment>\<open>Some pattern as sequence (no semicolon)\<close>
term \<open>\<lbrakk>
  #[fuel(\<epsilon>\<open>n :: nat\<close>)]
  while let Some(v) = Some(g) {
    ()
  }
  ()
\<rbrakk>\<close>

\<comment>\<open>Ok pattern\<close>
term \<open>\<lbrakk>
  #[fuel(\<epsilon>\<open>n\<close>)]
  while let Ok(v) = Ok(g) {
    ()
  };
  ()
\<rbrakk>\<close>

\<comment>\<open>Tuple pattern\<close>
term \<open>\<lbrakk>
  #[fuel(\<epsilon>\<open>n\<close>)]
  while let (a, b) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
    ()
  };
  ()
\<rbrakk>\<close>

end
subsection\<open>Control Flow - Return\<close>

subsubsection\<open>Return Without Value\<close>

term\<open>\<lbrakk>
  return;
\<rbrakk>\<close>

term\<open>(FunctionBody \<lbrakk>
  {return;}; return;
\<rbrakk>)\<close>

subsubsection\<open>Return With Value\<close>

term\<open>\<lbrakk>
  let v = \<llangle>42 :: 64 word\<rrangle>;
  return v;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let (a,b) = (1,2);
  return;
\<rbrakk>\<close>

subsubsection\<open>Return in Control Flow\<close>

definition test :: \<open>(nat, unit, unit, unit, unit) function_body\<close> where
  \<open>test \<equiv> (FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>)\<close>
hide_const test

term\<open>(FunctionBody \<lbrakk>
    let x = \<llangle>Some (0 :: nat)\<rrangle>;
    let Some(foo) = x else {
      return;
    };
    return;
  \<rbrakk>) :: (nat, unit, unit, unit, unit) function_body\<close>

context
  fixes x :: \<open>'s\<close>
  fixes g :: \<open>'s \<Rightarrow> ('a, nat option, unit, unit, unit) function_body\<close>
begin
term\<open>\<lbrakk>
  let blub = 0;
  if let Some(x) = g(x) {
    return 0;
  } else {
    return 42;
  };
  return 12;
\<rbrakk>\<close>
end

\<comment> \<open>Having a warning in the following test case is expected, see also RFC:
\<^url>\<open>https://rust-lang.github.io/rfcs/3137-let-else.html\<close>\<close>
term\<open>\<lbrakk>
  let x = if True { 0 } else { 1 };
  return x;
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = (if True { 0 } else { 1 });
  return x;
\<rbrakk>\<close>

subsection\<open>Control Flow - Error Propagation\<close>

subsubsection\<open>Propagation with Option\<close>

context
  fixes opt :: \<open>nat option\<close>
begin
term \<open>\<lbrakk> opt? \<rbrakk>\<close>
term \<open>\<lbrakk> let x = opt?; x \<rbrakk>\<close>
end

subsubsection\<open>Propagation with Result\<close>

context
  fixes res :: \<open>(nat, bool) result\<close>
begin
term \<open>\<lbrakk> res? \<rbrakk>\<close>
term \<open>\<lbrakk> let x = res?; x \<rbrakk>\<close>
end

subsection\<open>Data Structures - Tuples\<close>

subsubsection\<open>Tuple Construction\<close>

term\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, True, False)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  ((False, True), False)
\<rbrakk>\<close>

subsubsection\<open>Tuple Indexing\<close>

term\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == \<llangle>0 :: 32 word\<rrangle>);
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).1 == \<llangle>1 :: 32 word\<rrangle>);
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3 == 3);
  assert!(tup.4 == 4);
  assert!(tup.5 == 5);
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let tup = (\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>,
             \<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>, \<llangle>6 :: 32 word\<rrangle>, \<llangle>7 :: 32 word\<rrangle>,
             \<llangle>8 :: 32 word\<rrangle>, \<llangle>9 :: 32 word\<rrangle>, \<llangle>10 :: 32 word\<rrangle>, \<llangle>11 :: 32 word\<rrangle>,
             \<llangle>12 :: 32 word\<rrangle>, \<llangle>13 :: 32 word\<rrangle>, \<llangle>14 :: 32 word\<rrangle>, \<llangle>15 :: 32 word\<rrangle>);
  assert!(tup.6 == \<llangle>6 :: 32 word\<rrangle>);
  assert!(tup.10 == \<llangle>10 :: 32 word\<rrangle>);
  assert!(tup.15 == \<llangle>15 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let tup = (a, b, c, (False, True));
  assert!(tup.0 == 0);
  assert!(tup.1 == 1);
  assert!(tup.2 == 2);
  assert!(tup.3.0 == False);
  assert!(tup.3.1 == True);
\<rbrakk>\<close>

term\<open>\<lbrakk>
  assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)
\<rbrakk>\<close>

(*
TODO: Fix this bug
lemma \<open>\<lbrakk>assert!((\<llangle>0 :: 32 word\<rrangle>, \<llangle>1 :: 32 word\<rrangle>).0 == 0)\<rbrakk> = Expression (Success ())\<close>
  by simp
*)

subsubsection\<open>Tuple Destructuring\<close>

term\<open>\<lbrakk>
  let a = \<llangle>0 :: 32 word\<rrangle>;
  let b = \<llangle>1 :: 32 word\<rrangle>;
  let c = \<llangle>2 :: 32 word\<rrangle>;
  let d = \<llangle>3 :: 32 word\<rrangle>;
  let e = \<llangle>4 :: 32 word\<rrangle>;
  let f = \<llangle>5 :: 32 word\<rrangle>;
  let g = \<llangle>6 :: 32 word\<rrangle>;
  let h = \<llangle>7 :: 32 word\<rrangle>;
  let tup = (a, b, c, d, e, f, g, h);
  let (aa, bb, cc, dd, ee, ff, gg, hh) = tup;
  assert!(a == aa);
  assert!(b == bb);
  assert!(c == cc);
  assert!(d == dd);
  assert!(e == ee);
  assert!(f == ff);
  assert!(g == gg);
  assert!(h == hh);
  let tup2 = (a, (b, c));
  let (aaa, (bbb, ccc)) = tup2;
  assert!(aaa == a);
  assert!(bbb == b);
  assert!(ccc == c);
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let a = \<llangle>10 :: 32 word\<rrangle>;
  let b = \<llangle>20 :: 32 word\<rrangle>;
  let c = \<llangle>30 :: 32 word\<rrangle>;
  let tup = (a, (b, c));
  let (x, (y, z)) = tup;
  assert!(x == a);
  assert!(y == b);
  assert!(z == c)
\<rbrakk>\<close>

subsection\<open>Data Structures - Option and Result\<close>

subsubsection\<open>Option Construction\<close>

term\<open>\<lbrakk> Some(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
term\<open>\<lbrakk> None \<rbrakk>\<close>
term\<open>\<lbrakk> \<llangle>Some (0 :: nat)\<rrangle> \<rbrakk>\<close>

subsubsection\<open>Result Construction\<close>

term\<open>\<lbrakk> Ok(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>
term\<open>\<lbrakk> Err(\<llangle>42 :: nat\<rrangle>) \<rbrakk>\<close>

subsubsection\<open>Option/Result in Pattern Matching\<close>

text\<open>See earlier sections on match expressions for comprehensive examples.\<close>

subsection\<open>Data Structures - Ranges\<close>

subsubsection\<open>Exclusive Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x..y \<rbrakk>\<close>
end

subsubsection\<open>Inclusive Range\<close>

context
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> x..=y \<rbrakk>\<close>
term \<open>\<lbrakk> let rng = x ..= x+y; rng.is_empty() \<rbrakk>\<close>
end

subsubsection\<open>Inclusive Range Boundary Behavior\<close>

term\<open>\<lbrakk>
  let int_max = \<llangle>255 :: 8 word\<rrangle>;
  let inclusive = int_max ..= int_max;
  assert!(!(inclusive.is_empty()));
  assert!(inclusive.contains(int_max));
  let exclusive = int_max .. int_max;
  assert!(exclusive.is_empty());
  ()
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let mut count = \<llangle>0 :: 8 word\<rrangle>;
  let int_max = \<llangle>255 :: 8 word\<rrangle>;
  for i in int_max ..= int_max {
    count += \<llangle>1 :: 8 word\<rrangle>;
  };
  assert!(*count == \<llangle>1 :: 8 word\<rrangle>);
  ()
\<rbrakk>\<close>

subsubsection\<open>Range in For Loops\<close>

text\<open>See For Loop with Range subsection above.\<close>

subsection\<open>Functions and Closures\<close>

subsubsection\<open>Function Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
  fixes h :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes i :: \<open>'s \<Rightarrow> 't \<Rightarrow> 'u \<Rightarrow> 's \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
begin

term\<open>\<lbrakk>
  h(a, b, c, a)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  i(a, b, c, a, b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  \<epsilon>\<open>g\<close>(c);
  g(c);
  f(a,b);
  a.f(b);
  f(g(c),b);
  g(c).f(b)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  f(g(c),b)
\<rbrakk>\<close>

end

subsubsection\<open>Method-Style Calls\<close>

context
  fixes a :: \<open>'s\<close>
  fixes b :: \<open>'t\<close>
  fixes c :: \<open>'u\<close>
  fixes f :: \<open>'s \<Rightarrow> 't \<Rightarrow> ('a, 'b, unit, unit, unit) function_body\<close>
  fixes g :: \<open>'u \<Rightarrow> ('a, 's, unit, unit, unit) function_body\<close>
begin

term\<open>\<lbrakk>
  g(c);
  c.g();
\<rbrakk>\<close>

term\<open>\<lbrakk>
  a.f(b)
\<rbrakk>\<close>

end

subsubsection\<open>Turbofish Syntax\<close>

context
  fixes f :: \<open>nat \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
  fixes g :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, 'a, unit, unit, unit) function_body\<close>
begin
term \<open>\<lbrakk> f::<5>() \<rbrakk>\<close>
term \<open>\<lbrakk> g::<10>(True) \<rbrakk>\<close>
end

subsubsection\<open>Closures\<close>

context
  fixes f :: \<open>nat \<Rightarrow> bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body\<close>
  fixes h :: \<open>nat \<Rightarrow> (bool \<Rightarrow> ('s, nat, unit, unit, unit) function_body) \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
  fixes n :: \<open>nat\<close>
begin
term \<open>\<lbrakk> || return x; \<rbrakk>\<close>
term \<open>\<lbrakk> |x| x \<rbrakk>\<close>
term \<open>\<lbrakk> |x, y| { let z = f(x,y); return z; }  \<rbrakk>\<close>
term \<open>\<lbrakk> h(n, |b| { let z = f(n,b); return \<llangle>n+z\<rrangle>; }) \<rbrakk>\<close>
end

subsection\<open>References and Mutation\<close>

subsubsection\<open>Mutable Bindings\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  x
\<rbrakk>\<close>

subsubsection\<open>Borrow Syntax\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
  fixes x y :: \<open>32 word\<close>
begin
term \<open>\<lbrakk> &r \<rbrakk>\<close>
term \<open>\<lbrakk> &mut r \<rbrakk>\<close>
term \<open>\<lbrakk> x & y \<rbrakk>\<close>
end

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  let xr = &x;
  let xw = &mut x;
  xw
\<rbrakk>\<close>

subsubsection\<open>Dereference\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
begin

private definition dummy_dereference_ref :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_ref \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref

term \<open>\<lbrakk> *r \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref
end

subsubsection\<open>Double Dereference\<close>

context
  fixes rr :: \<open>('s, 'b, ('s, 'b, integer) Global_Store.ref) Global_Store.ref\<close>
begin

private definition dummy_dereference_ref2 :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_ref2 \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref2

term \<open>\<lbrakk> **rr \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_ref2
end

subsubsection\<open>Assignment\<close>

term\<open>\<lbrakk>
  let mut x = \<llangle>0 :: 32 word\<rrangle>;
  *x = \<llangle>42 :: 32 word\<rrangle>;
  x
\<rbrakk>\<close>

subsection\<open>Field Access and Records\<close>

subsubsection\<open>Test Record Definitions\<close>

datatype_record testrec =
  field1 :: integer
  field2 :: bool
micro_rust_record testrec

datatype_record testrec2 =
  field3 :: testrec
  field4 :: \<open>bool option\<close>
micro_rust_record testrec2

subsubsection\<open>Simple Field Access\<close>

context
  fixes x :: testrec
  fixes y :: testrec2
begin
term\<open> \<lbrakk> x \<rbrakk> \<close>
term \<open>\<lbrakk> x.field1 \<rbrakk>\<close>
term \<open>\<lbrakk> y.field4 \<rbrakk>\<close>
end

subsubsection\<open>Nested Field Access\<close>

context
  fixes y :: testrec2
begin
value \<open>\<lbrakk> y.field3.field1 \<rbrakk>\<close>
end

subsubsection\<open>Declaring \<^verbatim>\<open>micro_rust_record\<close>s in locales\<close>
locale micro_rust_record_locale_test =
  fixes answer :: \<open>64 word\<close>
  assumes \<open>answer = 42\<close>
begin

datatype_record foobar =
  field5 :: \<open>64 word\<close>
  field6 :: \<open>64 word\<close>
micro_rust_record foobar

term \<open>\<lambda> x :: foobar. \<lbrakk> x.field5 + x.field6 \<rbrakk>\<close>
term \<open>\<lambda> x :: ('addr, 'fv, foobar) ref. \<lbrakk> *x.field5 + *x.field6 \<rbrakk>\<close>

end

subsubsection\<open>Field Assignment Through Lenses\<close>

context
  fixes r :: \<open>('s, 'b, integer) Global_Store.ref\<close>
  fixes s :: \<open>('s, 'b, testrec2) Global_Store.ref\<close>
  fixes f :: \<open>('s, 'b, integer) Global_Store.ref \<Rightarrow> integer \<Rightarrow> ('s, unit, unit, unit, unit) function_body\<close>
begin

private definition dummy_dereference_field :: \<open>('s, 'b, 'v) Global_Store.ref \<Rightarrow> ('s, 'v, unit, unit, unit) function_body\<close> where
  \<open>dummy_dereference_field \<equiv> undefined\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field

term\<open>field4_lens\<close>
term \<open>\<lbrakk> r.f(10) \<rbrakk>\<close>
term\<open>bindlift2 focus_const (literal s) (literal field3_lens)\<close>
term \<open>\<lbrakk> *(s. field3_lens) \<rbrakk>\<close>
term\<open>store_dereference_const s\<close>
term \<open>\<lbrakk> (*s). field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = *r \<rbrakk>\<close>
term \<open>\<lbrakk> r = (*s).field3_lens.field1_lens \<rbrakk>\<close>
term \<open>\<lbrakk> r = *s.field3_lens.field1_lens \<rbrakk>\<close>

term \<open>\<lbrakk> r = 10 \<rbrakk>\<close>
term \<open>\<lbrakk> *(s.field4_lens) \<rbrakk>\<close>
term \<open>\<lbrakk> (*s).field4_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field1_lens = *r \<rbrakk>\<close>
term \<open>\<lbrakk> *r \<rbrakk>\<close>

term \<open>\<lbrakk> s.field3_lens \<rbrakk>\<close>
term \<open>\<lbrakk> s.field3_lens.field2_lens \<rbrakk>\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> dummy_dereference_field
end

subsubsection\<open>Custom uRust Field Names\<close>

text\<open>By default \<^verbatim>\<open>micro_rust_record\<close> registers each field's lens under the
bare HOL field name. Since HOL field names are usually disambiguated with a
record-name prefix (e.g. \<open>bounds_rec_lo\<close>), this forces that prefix to be
repeated at every uRust use site. The optional \<^verbatim>\<open>(hol_field = "urust_name", \<dots>)\<close>
mapping overrides the uRust name per field, so one can write the un-prefixed
\<open>m.lo\<close> in uRust while the HOL field stays \<open>bounds_rec_lo\<close>.\<close>

datatype_record bounds_rec =
  bounds_rec_lo :: \<open>64 word\<close>
  bounds_rec_hi :: \<open>64 word\<close>
  bounds_rec_flag :: bool
micro_rust_record bounds_rec
  (bounds_rec_lo = "lo",
   bounds_rec_hi = "end",
   bounds_rec_flag = "flag")

text\<open>Each custom name parses at a uRust use site and resolves to its own,
correctly-typed field lens. Note \<open>end\<close> is an Isabelle keyword, yet is accepted
as a field name in \<open>m.end\<close>.\<close>

context
  fixes m :: bounds_rec
begin
term \<open>\<lbrakk> m.lo \<rbrakk>\<close>
term \<open>\<lbrakk> m.end \<rbrakk>\<close>
term \<open>\<lbrakk> m.flag \<rbrakk>\<close>

text\<open>The custom name is definitionally the same access as the underlying
record-prefixed lens — i.e. the override only renames, it does not change the
target.\<close>
lemma \<open>\<lbrakk> m.lo \<rbrakk>   = \<lbrakk> m.bounds_rec_bounds_rec_lo_lens \<rbrakk>\<close>   by (rule refl)
lemma \<open>\<lbrakk> m.end \<rbrakk>  = \<lbrakk> m.bounds_rec_bounds_rec_hi_lens \<rbrakk>\<close>   by (rule refl)
lemma \<open>\<lbrakk> m.flag \<rbrakk> = \<lbrakk> m.bounds_rec_bounds_rec_flag_lens \<rbrakk>\<close> by (rule refl)
end

text\<open>Concrete evaluation confirms each custom name reads back the right field:
\<open>lo\<close>, \<open>end\<close> and \<open>flag\<close> recover the first, second and third
constructor arguments respectively — so the three names target three distinct
fields and are not aliased to one.\<close>
value [simp] \<open>\<lbrakk> \<llangle>make_bounds_rec 1 2 True\<rrangle>.lo \<rbrakk>\<close>   \<comment> \<open>\<open>Expression (Success 1)\<close>\<close>
value [simp] \<open>\<lbrakk> \<llangle>make_bounds_rec 1 2 True\<rrangle>.end \<rbrakk>\<close>  \<comment> \<open>\<open>Expression (Success 2)\<close>\<close>
value [simp] \<open>\<lbrakk> \<llangle>make_bounds_rec 1 2 True\<rrangle>.flag \<rbrakk>\<close> \<comment> \<open>\<open>Expression (Success True)\<close>\<close>

text\<open>An override replaces the default name rather than adding to it: once
\<open>bounds_rec_lo\<close> is mapped to \<open>lo\<close>, the field is reachable in uRust only as
\<open>m.lo\<close>, not under the record-prefixed HOL name.\<close>

subsubsection\<open>Partial uRust Field-Name Overrides\<close>

text\<open>A mapping need not mention every field: fields omitted from the mapping
keep their default (bare HOL) name, while listed fields are renamed.\<close>

datatype_record partial_override_rec =
  por_renamed :: \<open>32 word\<close>
  por_kept    :: \<open>32 word\<close>
micro_rust_record partial_override_rec
  (por_renamed = "renamed")

context
  fixes p :: partial_override_rec
begin
term \<open>\<lbrakk> p.renamed \<rbrakk>\<close>   \<comment> \<open>renamed field uses the override\<close>
term \<open>\<lbrakk> p.por_kept \<rbrakk>\<close>  \<comment> \<open>omitted field keeps its HOL name\<close>
end

value [simp] \<open>\<lbrakk> \<llangle>make_partial_override_rec 7 8\<rrangle>.renamed \<rbrakk>\<close>
value [simp] \<open>\<lbrakk> \<llangle>make_partial_override_rec 7 8\<rrangle>.por_kept \<rbrakk>\<close>

subsubsection\<open>Default Registration (no mapping) Still Works\<close>

text\<open>Omitting the mapping entirely behaves exactly as before: fields are
registered under their bare HOL names.\<close>

datatype_record no_override_rec =
  nor_a :: \<open>32 word\<close>
  nor_b :: bool
micro_rust_record no_override_rec

context
  fixes n :: no_override_rec
begin
term \<open>\<lbrakk> n.nor_a \<rbrakk>\<close>
term \<open>\<lbrakk> n.nor_b \<rbrakk>\<close>
end

subsubsection\<open>Custom Names on Nested Records\<close>

text\<open>Custom field names compose through nested field access just like the
default names do.\<close>

datatype_record inner_named =
  inner_named_value :: \<open>32 word\<close>
micro_rust_record inner_named (inner_named_value = "value")

datatype_record outer_named =
  outer_named_inner :: inner_named
  outer_named_flag  :: bool
micro_rust_record outer_named
  (outer_named_inner = "inner",
   outer_named_flag  = "flag")

context
  fixes o :: outer_named
begin
term \<open>\<lbrakk> o.inner \<rbrakk>\<close>
term \<open>\<lbrakk> o.flag \<rbrakk>\<close>
value \<open>\<lbrakk> o.inner.value \<rbrakk>\<close>
end

value [simp] \<open>\<lbrakk> \<llangle>make_outer_named (make_inner_named 99) False\<rrangle>.inner.value \<rbrakk>\<close>

subsubsection\<open>Custom Names in a Locale\<close>

text\<open>The mapping is honoured for \<^verbatim>\<open>micro_rust_record\<close>s declared inside a
locale, mirroring the default-name locale test above.\<close>

locale micro_rust_record_override_locale_test =
  fixes answer :: \<open>64 word\<close>
  assumes \<open>answer = 42\<close>
begin

datatype_record loc_named =
  loc_named_lo :: \<open>64 word\<close>
  loc_named_hi :: \<open>64 word\<close>
micro_rust_record loc_named
  (loc_named_lo = "lo",
   loc_named_hi = "hi")

term \<open>\<lambda> x :: loc_named. \<lbrakk> x.lo + x.hi \<rbrakk>\<close>
term \<open>\<lambda> x :: ('addr, 'fv, loc_named) ref. \<lbrakk> *x.lo + *x.hi \<rbrakk>\<close>

end

subsection\<open>Macros\<close>

subsubsection\<open>Assertion Macros\<close>

context
  fixes b :: \<open>bool\<close>
  fixes o :: \<open>nat option\<close>
  fixes a_value :: \<open>32 word\<close>
  fixes x y :: \<open>nat\<close>
begin
term \<open>\<lbrakk> assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert!( b ) \<rbrakk>\<close>
term \<open>\<lbrakk> assert!(!o.is_none()) \<rbrakk>\<close>
term\<open>\<lbrakk> assert!(b); a_value as u16\<rbrakk>\<close>
term\<open>\<lbrakk> assert!(a_value as usize == a_value as usize); a_value as u16\<rbrakk>\<close>
term \<open>\<lbrakk> assert_eq!(x, y) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_ne!(x, y) \<rbrakk>\<close>
term \<open>\<lbrakk> assert!(b, "ignored assertion message") \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert!(b, "ignored debug assertion message", x) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_eq!(x, y, "ignored assert_eq message", x) \<rbrakk>\<close>
term \<open>\<lbrakk> assert_ne!(x, y, "ignored assert_ne message", y) \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert_eq!(x, y, "ignored debug_assert_eq message") \<rbrakk>\<close>
term \<open>\<lbrakk> debug_assert_ne!(x, y, "ignored debug_assert_ne message") \<rbrakk>\<close>
end

subsubsection\<open>Error Macros\<close>

context
  fixes msg :: \<open>String.literal\<close>
  and idx :: \<open>32 word\<close>
  and r :: \<open>('a, 'b, 'v) ref\<close>
begin
term \<open>\<lbrakk> panic!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!(msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("some_fun") \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!(nm) \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("oh no!") \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!("yikes!") \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!( \<llangle>''yikes!''\<rrangle> ) \<rbrakk>\<close>
term \<open>\<lbrakk> panic!() \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!() \<rbrakk>\<close>
term \<open>\<lbrakk> todo!() \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!() \<rbrakk>\<close>
term \<open>\<lbrakk> panic!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> fatal!("first", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> unreachable!() \<rbrakk>\<close>
term \<open>\<lbrakk> unreachable!("should not reach here") \<rbrakk>\<close>
term \<open>\<lbrakk> unreachable!("bad state: {}", msg) \<rbrakk>\<close>
term \<open>\<lbrakk> panic!("Invalid index: {}", idx) \<rbrakk>\<close>
term \<open>\<lbrakk> unimplemented!("not done: {} {}", idx, idx) \<rbrakk>\<close>
term \<open>\<lbrakk> todo!("implement: {}", idx) \<rbrakk>\<close>
term \<open>\<lbrakk> addr_of!(r) \<rbrakk>\<close>
term \<open>\<lbrakk> addr_of_mut!(r) \<rbrakk>\<close>
end

subsubsection\<open>Logging\<close>

context
  fixes b :: \<open>bool\<close>
begin
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[LogNat 32]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>[LogNat 32, LogString (String.implode ''goo'')]\<rrangle> \<rbrakk>\<close>
term \<open>\<lbrakk> \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>[LogBool b]\<rrangle> \<rbrakk>\<close>
end

subsection\<open>Miscellaneous Features\<close>

subsubsection\<open>Unsafe Blocks\<close>

context
  fixes msg :: \<open>String.literal\<close>
begin
term \<open>\<lbrakk> unsafe { panic!("msg") } \<rbrakk>\<close>
end

subsubsection\<open>Array and Slice Expression Literals\<close>

term \<open>\<lbrakk> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> &[\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> & mut [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> & mut [] \<rbrakk>\<close>
term \<open>\<lbrakk> [\<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>];
  assert!(xs[0] == \<llangle>1 :: 32 word\<rrangle>);
  assert!(xs[2] == \<llangle>3 :: 32 word\<rrangle>)
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = &[\<llangle>4 :: 32 word\<rrangle>, \<llangle>5 :: 32 word\<rrangle>];
  let s = match xs {
    [a, b] \<Rightarrow> a + b,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  };
  assert!(s == \<llangle>9 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Vec Macro\<close>

term \<open>\<lbrakk> vec![\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>, \<llangle>3 :: 32 word\<rrangle>] \<rbrakk>\<close>
term \<open>\<lbrakk> vec![] \<rbrakk>\<close>

term\<open>\<lbrakk>
  let xs = vec![\<llangle>10 :: 32 word\<rrangle>, \<llangle>20 :: 32 word\<rrangle>];
  assert!(xs[0] == \<llangle>10 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Matches Macro\<close>

context
  fixes x :: \<open>nat option\<close>
  and y :: \<open>bool option\<close>
begin
term \<open>\<lbrakk> matches!(x, Some(_)) \<rbrakk>\<close>
term \<open>\<lbrakk> matches!(x, None) \<rbrakk>\<close>
term \<open>\<lbrakk> matches!(y, Some(true) | None) \<rbrakk>\<close>
end

subsubsection\<open>Indexing\<close>

context
  fixes xs :: \<open>nat list\<close>
  fixes xss :: \<open>nat list list\<close>
begin
term \<open>\<lbrakk> xs [0..100][42] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10] \<rbrakk>\<close>
term \<open>\<lbrakk> xss[10][100] \<rbrakk>\<close>
end

subsubsection\<open>Const Bindings\<close>

term\<open>\<lbrakk>
  const FOO = 5;
  ()
\<rbrakk>\<close>

subsubsection\<open>Scoping and Block Expressions\<close>

context
  fixes x :: \<open>'s\<close>
begin
term\<open>\<lbrakk> 1 \<rbrakk> :: ('s, nat, 'r, 'abort, 'i, 'o) expression\<close>
end

subsubsection\<open>Sequencing\<close>

term\<open>\<lbrakk>
  let a = 1;
  let b = 2;
  a
\<rbrakk>\<close>

subsection\<open>Rust Path Expressions\<close>

text\<open>Experiment block with path notation tests\<close>

experiment
  notes [[syntax_ast_trace]]
begin

term\<open>3 :: 64 word\<close>

definition number_42 :: nat where \<open>number_42 \<equiv> 42\<close>

micro_rust_notation (literal) number_42 ("foo::bar::test1")
micro_rust_notation (literal) number_42 ("foo::bar::test2")
micro_rust_notation (literal) True ("foo::bar::test3")

definition \<open>the_record \<equiv> make_testrec 1 False\<close>

micro_rust_notation (literal) the_record ("the::record")

term\<open>\<lbrakk>the::record\<rbrakk>\<close>
term\<open>\<lbrakk>(the::record).field1\<rbrakk>\<close>
term\<open>\<lbrakk>the::record.field1\<rbrakk>\<close>

term\<open>(1, 2)\<close>

term\<open>\<lbrakk> foo::bar::test1 \<rbrakk>\<close>
term\<open>\<lbrakk> foo::bar:: test2 \<rbrakk>\<close>
term\<open>\<lbrakk> foo:: bar::test3 \<rbrakk>\<close>

datatype test =
    Test1
  | Test2

micro_rust_notation (literal) test.Test1 ("test::Test_1")
micro_rust_notation (literal) test.Test2 ("test::Test_2")

definition plus_two :: \<open>'l::len word \<Rightarrow> 'l word\<close> where \<open>plus_two n \<equiv> n + 2\<close>
definition \<open>plus_two_lift \<equiv> lift_fun1 plus_two\<close>

micro_rust_notation (call)    plus_two_lift ("plus2::lifted")
micro_rust_notation (literal) plus_two_lift ("plus2::lifted")
  \<comment>\<open>Registered under both function- and literal-kind: the test below
     uses \<^verbatim>\<open>plus2::lifted(three)\<close> in function position and
     \<^verbatim>\<open>let fun = plus2::lifted\<close> in literal position.\<close>

definition three :: \<open>64 word\<close> where \<open>three = 3\<close>
micro_rust_notation (literal) three ("number::three")

term\<open>\<lbrakk> test::Test_1 \<rbrakk>\<close>

term\<open>\<lbrakk>plus2::lifted(three)\<rbrakk>\<close>
term\<open>\<lbrakk>plus_two_lift(three)\<rbrakk>\<close>
term\<open>\<lbrakk>
  let arg = test::Test_1;
  let fun = plus2::lifted;
  match arg {
    test::Test_1 \<Rightarrow> fun(three),
    test::Test_2 \<Rightarrow> plus2::lifted(three)
  }
\<rbrakk>\<close>


term\<open>\<lbrakk>
  let x = 5;
  match x {
    2 \<Rightarrow> False,
    number::three \<Rightarrow> False,
    0 \<Rightarrow> False,
    1 \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let x = 5;
\<comment> \<open>\<^verbatim>\<open>match_switch\<close> forces interpretation of this \<^verbatim>\<open>match\<close> clause as a \<^verbatim>\<open>switch\<close>\<close>
  match_switch x {
    number::three \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>

end

subsection\<open>Disjunctive Patterns\<close>

text\<open>For testing non-exhaustive disjunctive patterns in @{text "if let"} and @{text "let else"},
we need a type with more than two constructors. Using @{type option} or @{type result} with
disjunctive patterns that cover all constructors causes HOL's case expression machinery to
complain about redundant clauses (the implicit wildcard fallback becomes unreachable).\<close>

datatype three_case = CaseA nat | CaseB nat | CaseC

subsubsection\<open>Basic Match with Disjunctive Pattern\<close>

term\<open>\<lbrakk>
  match Some(\<llangle>42 :: nat\<rrangle>) {
    Some(x) | None \<Rightarrow> x
  }
\<rbrakk>\<close>

subsubsection\<open>Multiple Alternatives\<close>

context
  fixes x :: \<open>32 word\<close>
begin
term\<open>\<lbrakk>
  match_switch x {
    1 | 2 | 3 \<Rightarrow> True,
    _ \<Rightarrow> False
  }
\<rbrakk>\<close>
end

subsubsection\<open>Disjunctive Pattern with Guard\<close>

context
  fixes x :: \<open>32 word option\<close>
begin
term\<open>\<lbrakk>
  match x {
    Some(y) | None if y > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle>
  }
\<rbrakk>\<close>
end

subsubsection\<open>If-Let with Disjunctive Pattern\<close>

text\<open>Using @{type three_case} with only two alternatives ensures non-exhaustiveness,
so the implicit wildcard fallback is not redundant.\<close>

term\<open>\<lbrakk>
  if let CaseA(x) | CaseB(x) = \<llangle>CaseA 42\<rrangle> {
    ()
  }
\<rbrakk>\<close>

term\<open>\<lbrakk>
  if let CaseA(x) | CaseB(x) = \<llangle>CaseA 5\<rrangle> {
    assert!(x == \<llangle>5 :: nat\<rrangle>);
    ()
  } else {
    ()
  }
\<rbrakk>\<close>

subsubsection\<open>Let-Else with Disjunctive Pattern\<close>

text\<open>Using @{type three_case} ensures the disjunctive pattern is non-exhaustive.\<close>

term\<open>\<lbrakk>
  let CaseA(x) | CaseB(x) = \<llangle>CaseA 7\<rrangle> else {
    return;
  };
  x
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let CaseA(x) | CaseB(x) = \<llangle>CaseB 10\<rrangle> else {
    ()
  };
  assert!(x == \<llangle>10 :: nat\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Nested Disjunctive Patterns\<close>

term\<open>\<lbrakk>
  match Some(Ok(\<llangle>1 :: nat\<rrangle>)) {
    Some(Ok(x) | Err(x)) \<Rightarrow> x,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  }
\<rbrakk>\<close>

subsubsection\<open>Match-Switch with Disjunctive Numeric Patterns\<close>

context
  fixes x :: \<open>64 word\<close>
begin
term\<open>\<lbrakk>
  match_switch x {
    0 | 1 \<Rightarrow> False,
    _ \<Rightarrow> True
  }
\<rbrakk>\<close>
end

subsubsection\<open>Disjunctive Pattern with Result\<close>

term\<open>\<lbrakk>
  let res = match Ok(\<llangle>10 :: 32 word\<rrangle>) {
    Ok(x) | Err(x) \<Rightarrow> x
  };
  assert!(res == \<llangle>10 :: 32 word\<rrangle>)
\<rbrakk>\<close>

subsubsection\<open>Multiple Disjunctions in One Match\<close>

term\<open>\<lbrakk>
  match (Some(\<llangle>1 :: nat\<rrangle>), Some(\<llangle>2 :: nat\<rrangle>)) {
    (Some(x), Some(y)) | (None, Some(y)) \<Rightarrow> y,
    _ \<Rightarrow> \<llangle>0 :: nat\<rrangle>
  }
\<rbrakk>\<close>

subsubsection\<open>Mutable Pattern Destructuring\<close>

term\<open>\<lbrakk>
  let mut (x, y) = (\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>);
  x + y
\<rbrakk>\<close>

term\<open>\<lbrakk>
  let mut (a, b, c) = (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>);
  a
\<rbrakk>\<close>


section\<open>Legacy notation registration tests\<close>

locale Legacy_Notation_Tests =
  fixes legacy_notation_dummy :: unit
begin


definition my_test_some :: \<open>nat \<Rightarrow> nat option\<close> where
  \<open>my_test_some x = Some x\<close>

\<comment>\<open>Register in literal context: bare \<open>MyTestSome\<close> in value position
  takes the \<open>_shallow_identifier_as_literal\<close> path.\<close>
micro_rust_notation my_test_some ("MyTestSome")
print_micro_rust_notations

text\<open>\<^verbatim>\<open>\<lbrakk> MyTestSome \<rbrakk>\<close> resolves to a literal whose value is
\<^const>\<open>my_test_some\<close>, NOT a free variable named \<open>MyTestSome\<close>.\<close>

term \<open>\<lbrakk> MyTestSome \<rbrakk>\<close>

\<comment>\<open>Acceptance test: the identifier resolves to the registered HOL
  constant, so the embedding is syntactically equal to \<open>literal
  my_test_some\<close>.\<close>
lemma test_my_test_some_dispatched:
  shows \<open>\<lbrakk> MyTestSome \<rbrakk> = literal my_test_some\<close>
  by (rule refl)

text\<open>Non-\<open>Const\<close> backend: register an arbitrary HOL expression. The
dispatch should still resolve, but the use-site markup should fall back
to the registration site (since there is no underlying constant for
ctrl-click to jump to).\<close>

micro_rust_notation \<open>1 + (1 :: nat)\<close> ("OnePlusOne")

term \<open>\<lbrakk> OnePlusOne \<rbrakk>\<close>

\<comment>\<open>Acceptance: the marker resolves to the registered expression.\<close>
lemma test_one_plus_one_dispatched:
  shows \<open>\<lbrakk> OnePlusOne \<rbrakk> = literal (1 + (1 :: nat))\<close>
  by (rule refl)

text\<open>\<^verbatim>\<open>print_micro_rust_notations\<close> enumerates every entry in
\<^ML_structure>\<open>Micro_Rust_Names\<close> --- e.g. the \<open>Some\<close>/\<open>Ok\<close>/\<open>Err\<close> and
std-lib registrations in scope.\<close>

print_micro_rust_notations


subsection\<open>Shadow detection\<close>

text\<open>The dispatcher rejects --- and warns about --- registrations whose
\<^emph>\<open>rust\<close>-name accidentally collides with an existing HOL constant. The
fixture below sets up two HOL constants and uses them via dispatch
markers to trigger both branches of the check.\<close>

context begin

\<comment>\<open>HOL constant whose type matches what we then register: \<open>nat \<Rightarrow> nat\<close>.\<close>
private definition shadow_target_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_target_const x = x + 1\<close>

\<comment>\<open>HOL constant of a different type, used to test the warning branch.\<close>
private definition shadow_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>shadow_warn_const x = (x = 0)\<close>

\<comment>\<open>An unrelated backend we will register under each shadow name.\<close>
private definition shadow_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_backend x = x\<close>

\<comment>\<open>Register the backend under names that collide with the HOL constants.
  Registration itself is silent; the check fires at use time.\<close>
micro_rust_notation shadow_backend ("shadow_target_const")
micro_rust_notation shadow_backend ("shadow_warn_const")

text\<open>\<^bold>\<open>Error path\<close> --- a HOL constant of \<^emph>\<open>matching\<close> type already exists.
The marker below triggers \<open>shadow_check\<close>'s \<open>error\<close>:

\<^verbatim>\<open>Ambiguous uRust notation \<open>shadow_target_const\<close>:
   a registered backend matches type nat \<Rightarrow> nat
   but the HOL constant "shadow_target_const" of type nat \<Rightarrow> nat also matches.\<close>

The line is left commented so the test theory still compiles; uncomment
to reproduce the error interactively.\<close>

\<comment>\<open>term \<open>(urust_dispatch (STR ''literal:shadow_target_const'') :: nat \<Rightarrow> nat)\<close>\<close>

text\<open>\<^bold>\<open>Warning path\<close> --- a HOL constant exists but its type does
\<^emph>\<open>not\<close> match this occurrence. Dispatch picks the registered backend and
emits a \<open>warning\<close> mentioning the shadowed constant. Compiles cleanly.

The warning attaches to the \<^emph>\<open>use site\<close> of \<open>shadow_warn_const\<close>
(plumbed via \<open>mk_marker\<close>), not to the surrounding \<open>term\<close> command, so
jEdit highlights the identifier itself.

We use a \<open>urust_dispatch\<close> marker directly here (rather than wrapping
in \<open>\<lbrakk> \<dots> \<rbrakk>\<close>) so the registered backend's bare \<open>nat \<Rightarrow> nat\<close>
type matches without needing a \<open>function_body\<close> lift.\<close>
term \<open>(urust_dispatch (STR ''literal:shadow_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

end


subsection\<open>Shadow-opt-out flags\<close>

text\<open>The \<open>[no_shadow_warning]\<close> and \<open>[no_shadow_error]\<close> brackets on
\<open>micro_rust_notation\<close> silence the corresponding diagnostic for the
named registration. Each flag is per-(kind, name); the underlying
warning / error logic is unchanged.\<close>

context begin

private definition silenced_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>silenced_warn_const _ = True\<close>

private definition silenced_target_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>silenced_target_const x = x\<close>

private definition silenced_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>silenced_backend x = x + 1\<close>

\<comment>\<open>Register the backends without flags; configure shadow checks
  separately afterwards via \<open>micro_rust_notation_config\<close>. This
  decouples the registration site from the silencing decision, and
  lets the user adjust either independently.\<close>
micro_rust_notation silenced_backend ("silenced_warn_const")
micro_rust_notation silenced_backend ("silenced_target_const")

\<comment>\<open>\<^bold>\<open>Warning silenced.\<close> The HOL constant
  \<^const>\<open>silenced_warn_const\<close> exists at type \<open>nat \<Rightarrow> bool\<close>; without
  the config below, dispatch at \<open>nat \<Rightarrow> nat\<close> would print the
  the uRust notation shadow warning.\<close>
micro_rust_notation (config) [shadow_no_warn] "silenced_warn_const"

term \<open>(urust_dispatch (STR ''literal:silenced_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>\<^bold>\<open>Error silenced.\<close> The HOL constant
  \<^const>\<open>silenced_target_const\<close> exists at \<open>nat \<Rightarrow> nat\<close>; without the
  config below, dispatch at \<open>nat \<Rightarrow> nat\<close> would error out as ambiguously
  shadowing. \<open>shadow_no_err\<close> on this name routes us silently to the
  registered backend.\<close>
micro_rust_notation (config) [shadow_no_err] "silenced_target_const"

term \<open>(urust_dispatch (STR ''literal:silenced_target_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

end


subsection\<open>Variant coverage\<close>

text\<open>Exercise every form of the consolidated \<open>micro_rust_notation\<close>
command --- the auto-infer paths for all three kinds, the forced-kind
paths in their happy and error cases, and the four \<open>shadow_*\<close> config
modes (set, clear, per-name, default).\<close>

context begin

\<comment>\<open>Auto-infer literal: a non-function, non-lens HOL term routes to
  literal kind (the default fallthrough in \<open>infer_kind_of_type\<close>).\<close>
private definition variant_lit :: \<open>nat\<close> where \<open>variant_lit = 0\<close>
micro_rust_notation variant_lit ("VariantLit")
term \<open>(urust_dispatch (STR ''literal:VariantLit'') NoWitness :: nat)\<close>

\<comment>\<open>Auto-infer function: a HOL term whose type ends in \<open>function_body\<close>
  routes to function kind. We use \<open>lift_fun1\<close>, the standard wrapper.\<close>
private definition variant_fn :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>variant_fn = lift_fun1 Suc\<close>
micro_rust_notation variant_fn ("VariantFn")
term \<open>(urust_dispatch (STR ''function:VariantFn'') NoWitness :: nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body)\<close>

\<comment>\<open>Forced-kind happy paths.\<close>
private definition variant_lit_forced :: \<open>nat\<close> where \<open>variant_lit_forced = 1\<close>
micro_rust_notation (literal) variant_lit_forced ("VariantLitForced")
term \<open>(urust_dispatch (STR ''literal:VariantLitForced'') NoWitness :: nat)\<close>

private definition variant_fn_forced :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>variant_fn_forced = lift_fun1 Suc\<close>
micro_rust_notation (call) variant_fn_forced ("VariantFnForced")
term \<open>(urust_dispatch (STR ''function:VariantFnForced'') NoWitness :: nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body)\<close>

text\<open>Forced-kind error paths. Each line below would error with
``forced kind does not match the registered term's type'' if
uncommented; we keep them as commented-out smoke tests so the file
builds clean while documenting the expected behaviour.

\<^verbatim>\<open>micro_rust_notation (call)  variant_lit ("X")\<close>  -- term has type \<open>nat\<close>, not \<open>_ \<Rightarrow> _ function_body\<close>
\<^verbatim>\<open>micro_rust_notation (field) variant_lit ("Y")\<close>  -- term has type \<open>nat\<close>, not \<open>_ lens\<close>
\<^verbatim>\<open>micro_rust_notation (field) variant_fn  ("Z")\<close>  -- term has type \<open>_ \<Rightarrow> _ function_body\<close>, not \<open>_ lens\<close>\<close>

\<comment>\<open>Toggle off and back on: \<open>shadow_no_warn\<close> sets the bit;
  \<open>shadow_warn\<close> clears it.\<close>
private definition variant_warn_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>variant_warn_const _ = False\<close>
private definition variant_warn_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_warn_backend x = x\<close>
micro_rust_notation variant_warn_backend ("variant_warn_const")

\<comment>\<open>Set the suppression: this dispatch should NOT warn even though the
  HOL constant of differently-typed name exists.\<close>
micro_rust_notation (config) [shadow_no_warn] "variant_warn_const"
term \<open>(urust_dispatch (STR ''literal:variant_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Clear the suppression: this dispatch SHOULD warn again.\<close>
micro_rust_notation (config) [shadow_warn] "variant_warn_const"
term \<open>(urust_dispatch (STR ''literal:variant_warn_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Default-scope (no names): \<open>shadow_no_warn\<close> with no name argument
  silences the warning globally for the next dispatch.\<close>
private definition variant_default_const :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>variant_default_const _ = False\<close>
private definition variant_default_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_default_backend x = x\<close>
micro_rust_notation variant_default_backend ("variant_default_const")

\<comment>\<open>Globally suppress warnings; the dispatch below proceeds silently.\<close>
micro_rust_notation (config) [shadow_no_warn]
term \<open>(urust_dispatch (STR ''literal:variant_default_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>Restore warnings globally so we don't pollute later tests.\<close>
micro_rust_notation (config) [shadow_warn]

\<comment>\<open>Toggle off and back on for the error bit, mirroring the warning
  test above. We register a backend whose type matches an existing
  HOL constant (so without suppression the dispatch errors).\<close>
private definition variant_err_const :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_err_const x = x\<close>
private definition variant_err_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>variant_err_backend x = x + 1\<close>
micro_rust_notation variant_err_backend ("variant_err_const")

\<comment>\<open>Suppress the matching-shadow error and dispatch.\<close>
micro_rust_notation (config) [shadow_no_err] "variant_err_const"
term \<open>(urust_dispatch (STR ''literal:variant_err_const'') NoWitness :: nat \<Rightarrow> nat)\<close>

\<comment>\<open>The \<open>shadow_err\<close> mode (re-enable errors) flips the bit back.
  We don't actually re-dispatch here --- it would error --- but the
  command itself succeeds and toggles the bit.\<close>
micro_rust_notation (config) [shadow_err] "variant_err_const"

end


subsection\<open>Path-style names (\<^verbatim>\<open>Foo::Bar\<close>) via the new dispatcher\<close>

text\<open>\<^verbatim>\<open>lookup_id_tr\<close> consults \<^ML_structure>\<open>Micro_Rust_Names\<close> for
path-flattened identifiers (\<^verbatim>\<open>foo::bar\<close>) through the same single
identifier-resolution case it uses for plain names --- paths are flattened
into \<^verbatim>\<open>_urust_identifier_id\<close> earlier, so there is no separate path branch.
These tests exercise:

- short paths (\<open>foo::bar\<close>) registered via \<open>micro_rust_notation\<close>
  in literal and function positions;
- long paths (\<open>foo::bar.method()\<close>) where the head is resolved via
  the new dispatcher and the trailing method splits remain ordinary
  identifiers;
- multi-backend dispatch on a single path name (registering the same
  rust path for two distinct HOL terms differing only by type, then
  resolving by occurrence type).\<close>

context begin

text\<open>\<^bold>\<open>Short path, literal kind.\<close>\<close>

private definition path_lit_target :: \<open>nat\<close> where \<open>path_lit_target = 7\<close>
micro_rust_notation path_lit_target ("Foo::lit_value")

term \<open>\<lbrakk> Foo::lit_value \<rbrakk>\<close>

lemma test_path_lit_dispatched:
  shows \<open>\<lbrakk> Foo::lit_value \<rbrakk> = literal path_lit_target\<close>
  by (rule refl)


text\<open>\<^bold>\<open>Short path, function kind.\<close> A path-style \<^verbatim>\<open>Foo::bar\<close> in
function position must reach the dispatcher in the function kind
(\<^verbatim>\<open>NFunction\<close>) and resolve to the registered \<open>function_body\<close>-typed
backend. Shape-only smoke test: we just want the term to parse and
type-check via the new dispatch path.\<close>

private definition path_fn_target ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>path_fn_target = lift_fun1 Suc\<close>
micro_rust_notation path_fn_target ("Foo::add_one")

term \<open>\<lbrakk> Foo::add_one(0) \<rbrakk>\<close>


text\<open>\<^bold>\<open>Long path with method call.\<close> \<open>Foo::wrap(0)\<close> --- the head
\<open>Foo::wrap\<close> is a path identifier registered as a function backend via
the new command; the parenthesised argument is a function call.\<close>

private definition longpath_head ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>longpath_head x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation longpath_head ("Foo::wrap")

term \<open>\<lbrakk> Foo::wrap(0) \<rbrakk>\<close>


text\<open>\<^bold>\<open>Long path with method call.\<close> \<open>Bar::value.cont(0)\<close> --- this
exercises the long-path AST translator's \<^verbatim>\<open>_temporary_..._long_method\<close>
branch (\<^file>\<open>../Micro_Rust_Parsing_Legacy_Frontend/Micro_Rust_Syntax.thy\<close>),
which splits \<open>Bar::value.cont\<close> into:
- a path head \<open>"Bar::value"\<close> (literal kind): after AST flattening it is
  an ordinary \<^verbatim>\<open>_urust_identifier_id\<close> carrying the joined \<open>::\<close>-name,
  resolved by the same single table-lookup case in \<open>lookup_id_tr\<close> as a
  plain identifier;
- a method name \<open>cont\<close> (function kind, plain \<^verbatim>\<open>_urust_identifier_id\<close>).

Long-path field syntax (\<open>foo::bar.fld\<close>) goes through the same
translator with a different \<^verbatim>\<open>ast_joiner\<close>; we don't add an explicit
test for that since constructing a lens-typed field backend requires
more setup than these tests warrant, and the translator is already
exercised by the method-call shape.\<close>

private definition longpath_value :: \<open>nat\<close>
  where \<open>longpath_value = 13\<close>
private definition longpath_method ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>longpath_method self \<equiv> FunctionBody \<lbrakk> \<llangle>self\<rrangle> \<rbrakk>\<close>
micro_rust_notation longpath_value  ("Bar::value")
micro_rust_notation longpath_method ("cont")

term \<open>\<lbrakk> Bar::value.cont() \<rbrakk>\<close>


text\<open>\<^bold>\<open>Multi-backend dispatch on a path name.\<close> Register two distinct
HOL targets under the same path; the typed term-check phase picks the
unique match by occurrence type. Both backends are literals (so no
shadow check fires); the test asserts each route resolves to its own
backend.\<close>

private definition path_multi_nat :: \<open>nat \<Rightarrow> nat option\<close>
  where \<open>path_multi_nat n = Some n\<close>
private definition path_multi_bool :: \<open>bool \<Rightarrow> bool option\<close>
  where \<open>path_multi_bool b = Some b\<close>

micro_rust_notation path_multi_nat  ("Foo::ctor")
micro_rust_notation path_multi_bool ("Foo::ctor")

\<comment>\<open>Type-driven dispatch through the user-facing surface: the same path
  identifier \<^verbatim>\<open>Foo::ctor\<close> resolves to the \<open>nat\<close>-typed backend or the
  \<open>bool\<close>-typed backend depending on the use-site type ascription.

  (We previously also had explicit \<^verbatim>\<open>urust_dispatch (STR ''...'') NoWitness\<close>
  probes here, but the marker's payload representation is now an
  ML-internal \<^verbatim>\<open>Free\<close> with an encoded name and can't be written
  literally in source.)\<close>
lemma test_path_multi_dispatch_nat:
  shows \<open>(\<lbrakk> Foo::ctor \<rbrakk> :: ('s, nat \<Rightarrow> nat option, 'r, 'abort, 'i, 'o) expression)
       = literal path_multi_nat\<close>
  by (rule refl)

lemma test_path_multi_dispatch_bool:
  shows \<open>(\<lbrakk> Foo::ctor \<rbrakk> :: ('s, bool \<Rightarrow> bool option, 'r, 'abort, 'i, 'o) expression)
       = literal path_multi_bool\<close>
  by (rule refl)


text\<open>\<^bold>\<open>Shadowing on a path name (warning level).\<close> Mirrors the
plain-id warning test: the path's flattened source happens to look like
the qualified name of a HOL constant of mismatched type. Compiles
cleanly and prints a warning at the use site.\<close>

private definition shadow_path_target :: \<open>nat \<Rightarrow> bool\<close>
  where \<open>shadow_path_target _ = True\<close>
private definition shadow_path_backend :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>shadow_path_backend x = x\<close>

micro_rust_notation shadow_path_backend ("Shadow::path_target")
\<comment>\<open>No HOL constant called \<^verbatim>\<open>Shadow::path_target\<close> exists; this is
  not a shadow case at all --- this block is here as a smoke-test of
  the path-shape dispatch, not the shadow check (which fires only on
  bona-fide HOL constant collisions, indexed by Isabelle's name
  resolution).\<close>
term \<open>(urust_dispatch (STR ''literal:Shadow::path_target'') NoWitness :: nat \<Rightarrow> nat)\<close>

end

subsection\<open>Print-table sanity check (path entries enumerated)\<close>

text\<open>\<^verbatim>\<open>print_micro_rust_notations\<close> after the path registrations
above lists every entry, including the path-style ones. This is a
visual sanity check rather than a programmatic one --- the count is
non-zero by construction since the section above registers several.\<close>

print_micro_rust_notations


subsection\<open>Lambda / let / locale shadowing of registered names\<close>

text\<open>The dispatch pipeline must NOT emit a \<^const>\<open>urust_dispatch\<close>
marker for a uRust name that, at the use site, refers to a binder
(lambda-bound, let-bound, fixed-by-locale, or quantifier-bound) rather than
to a registered backend.

Concretely: registering \<^verbatim>\<open>("mask")\<close> as a field-kind notation must NOT
hijack a \<^emph>\<open>function parameter\<close> called \<^verbatim>\<open>mask\<close> when that parameter is
used at literal position inside the function body. The earlier
implementation of the legacy shim registered plain identifiers under
all three kinds for "compatibility" and so a literal-position \<open>mask\<close>
inside a \<open>\<lambda>mask. \<dots>\<close> would dispatch to the field's lens, breaking the
function definition with a "no backend matches type \<open>'l word\<close>" error.

These tests pin down the contract: same-named binders must win.\<close>

definition \<open>notation_foo \<equiv> 42\<close>
micro_rust_notation notation_foo ("bar")

term \<open>\<lbrakk> let foo = 12; bar \<rbrakk>\<close>


context begin

\<comment>\<open>Registered backends. The HOL targets are deliberately distinct from
  any of the binder names used below.\<close>

private definition shadow_test_lens :: \<open>('outer, 'inner) lens\<close>
  where \<open>shadow_test_lens \<equiv> undefined\<close>
private definition shadow_test_fn ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_test_fn \<equiv> lift_fun1 Suc\<close>
definition shadow_test_lit :: \<open>nat\<close>
  where \<open>shadow_test_lit = 99\<close>
  \<comment>\<open>Public so the \<open>shadow_no_shadow_test_dispatches\<close> sanity lemma
    below can unfold this via \<open>shadow_test_lit_def\<close>.\<close>

\<comment>\<open>Register the same name \<^verbatim>\<open>shdw\<close> in each of the three kinds, with
  three different HOL backends.\<close>
micro_rust_notation (field) shadow_test_lens ("shdw")
micro_rust_notation (call)  shadow_test_fn   ("shdw")
micro_rust_notation         shadow_test_lit  ("shdw")  \<comment>\<open>auto-infer: literal\<close>

text\<open>\<^bold>\<open>Lambda-bound binder.\<close> A function parameter named \<open>shdw\<close> must
shadow the registered backends inside the function body.\<close>

definition shadow_lambda_test ::
  \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_lambda_test \<equiv> \<lambda>shdw mask. FunctionBody \<lbrakk>
     \<comment> \<open>Both \<open>shdw\<close> and \<open>mask\<close> are lambda-bound function parameters; their
        in-body uses must NOT reach the dispatch table even though
        \<open>shdw\<close> has registrations under all three kinds.\<close>
     shdw + mask
   \<rbrakk>\<close>

lemma shadow_lambda_test_unaffected:
  shows \<open>shadow_lambda_test = (\<lambda>shdw mask. FunctionBody \<lbrakk> shdw + mask \<rbrakk>)\<close>
  unfolding shadow_lambda_test_def by (rule refl)
\<comment>\<open>If the dispatch had hijacked \<open>shdw\<close> or \<open>mask\<close>, the term on the
  right would type-check differently (or not at all).\<close>

text\<open>\<^bold>\<open>Let-bound binder.\<close> Same scenario via a \<^verbatim>\<open>let\<close> binding inside
the body.\<close>

definition shadow_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_let_test \<equiv> FunctionBody \<lbrakk>
     \<comment> \<open>\<open>shdw\<close> is bound by \<open>let\<close>; its later uses must come from the let,
        not from the table. \<open>64 word\<close> chosen so the body's \<open>+\<close>
        resolves via the registered word-arithmetic \<open>urust_add\<close>.\<close>
     let shdw = 7;
     shdw + shdw
   \<rbrakk>\<close>


text\<open>\<^bold>\<open>Mutable let-bound binder.\<close>\<close>

definition shadow_mut_let_test ::
  \<open>('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_mut_let_test \<equiv> FunctionBody \<lbrakk>
     let mut shdw = 7_u64;
     shdw = (8_u64);
   \<rbrakk>\<close>


subsection\<open>Position determines whether a binder can shadow a notation\<close>

text\<open>The three tests above all use \<open>shdw\<close> in \<^emph>\<open>value/operator\<close> position
(bare \<open>shdw\<close>, \<open>shdw + \<dots>\<close>, \<open>shdw = \<dots>\<close>), which dispatches in the \<^bold>\<open>literal\<close>
kind --- there a same-named \<open>let\<close>/\<open>\<lambda>\<close> binder legitimately shadows the
registration (Rust lexical scoping). The contract for the other two
positions is the opposite, and these tests pin it down:

  \<^item> \<^bold>\<open>call\<close> position \<open>x.shdw(\<dots>)\<close> / \<open>shdw(\<dots>)\<close>: a method/call head is a
    selector that can never be the local; the registered \<^bold>\<open>function\<close>
    notation \<^emph>\<open>wins\<close> over a same-named binder.
  \<^item> \<^bold>\<open>field\<close> position \<open>x.shdw\<close>: likewise a selector; the registered
    \<^bold>\<open>field\<close> notation wins.

\<open>shdw\<close> is registered in all three kinds (\<open>shadow_test_lens\<close> field,
\<open>shadow_test_fn\<close> call, \<open>shadow_test_lit\<close> literal); see
\<open>witness_takes_precedence\<close> in
\<^file>\<open>../Shallow_Micro_Rust_Base/Micro_Rust_Notations.thy\<close>.\<close>

text\<open>\<^bold>\<open>Literal position: binder wins.\<close> With a \<open>let shdw\<close> in scope, the
trailing bare \<open>shdw\<close> resolves to the \<open>let\<close>-bound \<open>7\<close>, NOT to the
registered literal \<open>shadow_test_lit = 99\<close>.\<close>

definition shadow_literal_binder_wins ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_literal_binder_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = 7;
     shdw
   \<rbrakk>\<close>

lemma shadow_literal_binder_wins_uses_binder:
  shows \<open>shadow_literal_binder_wins = FunctionBody \<lbrakk> let shdw = 7; shdw \<rbrakk>\<close>
  unfolding shadow_literal_binder_wins_def by (rule refl)
\<comment>\<open>The RHS \<open>shdw\<close> is the let-binder; had the literal notation hijacked
  it, this would mention \<open>shadow_test_lit\<close> and fail to be \<open>refl\<close>.\<close>

text\<open>\<^bold>\<open>Call position: function notation wins.\<close> Even with a same-named
\<open>let shdw\<close> in scope, the method head \<open>.shdw()\<close> resolves to the
registered \<open>shadow_test_fn\<close>, not the local. This is the \<open>x.f(f)\<close>
scenario in miniature: the \<open>shdw\<close> \<^emph>\<open>value\<close>
passed as the receiver is the binder, while the \<open>.shdw\<close> \<^emph>\<open>method\<close> head
is the notation. (\<open>shadow_test_fn :: nat \<Rightarrow> \<dots> function_body\<close> is unary,
so the no-arg method call \<open>r.shdw()\<close> supplies the receiver \<open>r\<close> as its
sole argument.)

The proof that the notation won is structural: the \<^emph>\<open>definition itself
type-checks\<close>. Had the \<open>let shdw\<close> binder hijacked the \<open>.shdw\<close> method
head, the head would be a \<open>nat\<close> local --- not callable --- and the body
would fail to parse/type-check.\<close>

definition shadow_call_notation_wins ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_call_notation_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = 0;
     shdw.shdw()
   \<rbrakk>\<close>
\<comment>\<open>The definition type-checking IS the test: the \<open>.shdw\<close> method head
  resolved to the registered \<open>shadow_test_fn\<close> (a \<open>function_body\<close>-typed
  call whose sole argument is the \<open>shdw\<close> receiver, the let-binder \<open>0\<close>).
  Had the \<open>let shdw\<close> binder captured the method head, it would be a
  \<open>nat\<close> local --- not callable --- and this definition would fail to
  type-check. (We assert via type-checking rather than an equality
  lemma, matching the call-position tests earlier in this file.)\<close>

text\<open>\<^bold>\<open>Field position: field notation wins.\<close> With a same-named \<open>let shdw\<close>
in scope, the field access \<open>r.shdw\<close> resolves to the registered
\<open>shadow_test_lens\<close>, not the local. This is the \<open>x.f\<close> selector
scenario: the \<open>.shdw\<close>
selector is the field, while the \<open>r\<close> receiver (here itself named
\<open>shdw\<close>) is the binder.

As with the call case, the proof is structural --- the definition only
type-checks because \<open>.shdw\<close> resolved to the \<open>shadow_test_lens\<close> lens; a
\<open>let\<close>-bound non-lens local could not be field-accessed.\<close>

definition shadow_field_notation_wins ::
  \<open>('s, 'inner, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_field_notation_wins \<equiv> FunctionBody \<lbrakk>
     let shdw = \<llangle>undefined :: 'outer\<rrangle>;
     shdw.shdw
   \<rbrakk>\<close>


text\<open>\<^bold>\<open>Free identifier with no binder and no registration.\<close> An
unregistered, unbound identifier should remain a free variable rather
than getting routed through dispatch.\<close>

term \<open>\<lbrakk> some_unregistered_name \<rbrakk>\<close>
  \<comment>\<open>Should print as \<open>literal some_unregistered_name\<close>, with
    \<open>some_unregistered_name\<close> a fresh free variable.\<close>


subsubsection\<open>Extended binder-shadow tests\<close>

text\<open>The tests in this subsection extend the basic
\<open>shadow_{lambda,let,mut_let}_test\<close> coverage above to every µRust
binder shape. Each test re-uses the \<^verbatim>\<open>shdw\<close>/\<^verbatim>\<open>mask\<close> registrations
declared earlier (literal/function/field). The contract under test is
the same in every case: a binder named like a registered notation must
shadow the registration in its body.

The proof method everywhere is \<open>by (rule refl)\<close> because the resolved
term is expected to have the bound variable as an in-scope binder use
(the \<open>\<up>\<close> arrow in the printer reflects the \<open>literal\<close> wrapper, but
the underlying \<open>Bound n\<close>/\<open>Free name\<close> is the same on both sides of the
equation).\<close>


text\<open>\<^bold>\<open>let with arithmetic body using the binder twice.\<close> Already
tested via \<open>shadow_let_test\<close> above; here we add a sequence-of-lets
form to exercise multiple successive binders where the inner one
shadows again.\<close>

definition shadow_nested_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_nested_let_test \<equiv> FunctionBody \<lbrakk>
     let shdw = 1_u64;
     let shdw = shdw + 2;
     shdw + 3
   \<rbrakk>\<close>

lemma shadow_nested_let_test_unaffected:
  shows \<open>shadow_nested_let_test = FunctionBody \<lbrakk>
     let shdw = 1_u64;
     let shdw = shdw + 2;
     shdw + 3
   \<rbrakk>\<close>
  unfolding shadow_nested_let_test_def by (rule refl)


text\<open>\<^bold>\<open>Let-else binder.\<close> The binder introduced by a
\<^verbatim>\<open>let \<dots> else \<dots>\<close> form must shadow the registration in the success-path
body, just like a plain \<^verbatim>\<open>let\<close>.\<close>

definition shadow_let_else_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_let_else_test \<equiv> FunctionBody \<lbrakk>
     let Some(shdw) = Some(7_u64) else { return 0_u64; };
     shdw + shdw
   \<rbrakk>\<close>

lemma shadow_let_else_test_unaffected:
  shows \<open>shadow_let_else_test = FunctionBody \<lbrakk>
     let Some(shdw) = Some(7_u64) else { return 0_u64; };
     shdw + shdw
   \<rbrakk>\<close>
  unfolding shadow_let_else_test_def by (rule refl)


text\<open>\<^bold>\<open>if-let binder.\<close> Same shadowing in the success branch of an
\<^verbatim>\<open>if let\<close> form.\<close>

definition shadow_if_let_test ::
  \<open>('s, unit, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_if_let_test \<equiv> FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       \<llangle>shdw + shdw\<rrangle>;
     }
   \<rbrakk>\<close>

lemma shadow_if_let_test_unaffected:
  shows \<open>shadow_if_let_test = FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       \<llangle>shdw + shdw\<rrangle>;
     }
   \<rbrakk>\<close>
  unfolding shadow_if_let_test_def by (rule refl)


text\<open>\<^bold>\<open>if-let-else binder.\<close> Both branches; the binder is in scope in
the success branch but not in the else branch.\<close>

definition shadow_if_let_else_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_if_let_else_test \<equiv> FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       shdw + shdw
     } else {
       0_u64
     }
   \<rbrakk>\<close>

lemma shadow_if_let_else_test_unaffected:
  shows \<open>shadow_if_let_else_test = FunctionBody \<lbrakk>
     if let Some(shdw) = Some(7_u64) {
       shdw + shdw
     } else {
       0_u64
     }
   \<rbrakk>\<close>
  unfolding shadow_if_let_else_test_def by (rule refl)


text\<open>\<^bold>\<open>match-arm constructor-with-args binder.\<close> A name introduced as a
constructor argument in a match arm shadows the registration in that
arm's RHS.\<close>

definition shadow_match_arm_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_match_arm_test \<equiv> FunctionBody \<lbrakk>
     match Some(7_u64) {
       Some(shdw) \<Rightarrow> shdw + shdw,
       None \<Rightarrow> 0_u64
     }
   \<rbrakk>\<close>

lemma shadow_match_arm_test_unaffected:
  shows \<open>shadow_match_arm_test = FunctionBody \<lbrakk>
     match Some(7_u64) {
       Some(shdw) \<Rightarrow> shdw + shdw,
       None \<Rightarrow> 0_u64
     }
   \<rbrakk>\<close>
  unfolding shadow_match_arm_test_def by (rule refl)


text\<open>\<^bold>\<open>Tuple destructuring let.\<close> Multiple binders introduced in one
\<^verbatim>\<open>let\<close> via tuple destructuring; each must shadow the registration in
the body.\<close>

definition shadow_tuple_let_test ::
  \<open>('s, 64 word, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_tuple_let_test \<equiv> FunctionBody \<lbrakk>
     let (shdw, mask) = (3_u64, 4_u64);
     shdw + mask
   \<rbrakk>\<close>

lemma shadow_tuple_let_test_unaffected:
  shows \<open>shadow_tuple_let_test = FunctionBody \<lbrakk>
     let (shdw, mask) = (3_u64, 4_u64);
     shdw + mask
   \<rbrakk>\<close>
  unfolding shadow_tuple_let_test_def by (rule refl)


text\<open>\<^bold>\<open>Closure parameter shadows the registration.\<close> A closure
parameter named \<^verbatim>\<open>shdw\<close> must shadow the same-named registration in
its body, exactly like a function parameter. The body of the closure
type-checks at \<open>64 word \<Rightarrow> 64 word\<close>, but lifted into the embedding,
so the test pins the closure's resolved shape via cartouche
equivalence.\<close>
term \<open>\<lbrakk> |shdw| { shdw + shdw } \<rbrakk>\<close>
  \<comment>\<open>The closure's body uses of \<open>shdw\<close> must be the closure binder, not
    a dispatch to \<open>shadow_test_lit\<close>. Inspection sanity check.\<close>


text\<open>\<^bold>\<open>Mixed: let-binder shadows registration; outside it, a
sibling closure with the same parameter name is independent.\<close> The
two binder slots are at different positions in the AST; both must
shadow the registration in their respective bodies.\<close>

term \<open>\<lbrakk>
  let shdw = 5_u64;
  shdw
\<rbrakk>\<close>

term \<open>\<lbrakk> let asdf = 42; asdf \<rbrakk>\<close>

  \<comment>\<open>Pre-condition: the let-binder shadows the registration.\<close>

term \<open>\<lbrakk> |shdw| { shdw + 1_u64 } \<rbrakk>\<close>
  \<comment>\<open>Pre-condition: the closure parameter shadows the registration.\<close>

\<comment>\<open>The combination form
   \<^verbatim>\<open>let shdw = ...; let inner = |shdw| { shdw + ... }; inner(shdw)\<close>
   is not currently accepted by the grammar (closures are not valid
   RHSes of \<open>let\<close>). The two single-binder tests above cover the
   shadowing semantics in each scope independently.\<close>


text\<open>\<^bold>\<open>Body that does NOT shadow uses the registration.\<close> Sanity
check: when a registered name is used WITHOUT a same-named binder, the
dispatch fires and we see the registered backend in the resolved term.
This is the contrast to the shadow tests --- it confirms the
registrations are still active.\<close>

definition shadow_no_shadow_test ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shadow_no_shadow_test \<equiv> FunctionBody \<lbrakk>
     \<comment>\<open>No \<open>shdw\<close> binder anywhere; the literal use must dispatch to
       the registered \<open>shadow_test_lit :: nat = 99\<close>.\<close>
     shdw
   \<rbrakk>\<close>

lemma shadow_no_shadow_test_dispatches:
  shows \<open>shadow_no_shadow_test = FunctionBody (literal 99)\<close>
  unfolding shadow_no_shadow_test_def shadow_test_lit_def by (rule refl)


text\<open>\<^bold>\<open>Path-style name shadowed by a binder is impossible by
construction\<close> --- you cannot bind a variable whose name contains \<^verbatim>\<open>::\<close>
in HOL. So the only shadow risk is the plain-identifier kind, which the
above tests cover.

We DO have to make sure path-style dispatch still fires when the same
name is registered as a path. The \<open>multi-backend dispatch on a path
name\<close> tests in the previous subsection cover this.\<close>


subsection\<open>Path identifier source-position markup\<close>

text\<open>The path AST translator merges per-segment source positions into
a single range covering the whole \<open>foo::bar(::\<dots>)\<close> form. \<open>lookup_id_tr\<close>
reads it back via \<open>source_positions_of\<close> so use-site markup highlights
the entire path. This is a visual sanity check --- the test below
processes cleanly and at jEdit time exposes the merged position by
ctrl-click on the path identifier landing back at the registration.\<close>

private definition shadow_path_lit :: \<open>nat\<close>
  where \<open>shadow_path_lit = 100\<close>
micro_rust_notation shadow_path_lit ("Markup::path::name")

term \<open>\<lbrakk> Markup::path::name \<rbrakk>\<close>


subsection\<open>Non-grammatical names (turbofish / macro forms)\<close>

text\<open>Names that are neither plain identifiers nor \<^verbatim>\<open>::\<close>-style paths ---
turbofish forms like \<open>Foo::<T>::new\<close> --- contain characters (\<open><\<close>, \<open>>\<close>)
that no µRust grammar production covers, so the surface token cannot be
parsed at all. The legacy adapter detects this via
\<^ML>\<open>Legacy_Micro_Rust_Notations.is_grammatical_name\<close> and emits a bespoke
\<^verbatim>\<open>syntax\<close> production (a new lexer token whose template IS the rust name)
plus a \<^verbatim>\<open>parse_ast_translation\<close> that rewrites the token to
the ordinary \<^verbatim>\<open>_urust_identifier_id\<close> AST node --- so it flows through the
exact same table-dispatch pipeline as a plain or path identifier (no
backend special-casing; type-directed dispatch, markup, and binder/field
precedence all apply). Without the production the dispatch-table entry
alone is useless: there is nothing to parse. These tests pin that the
bespoke path makes the turbofish use sites both \<^emph>\<open>parse\<close> and \<^emph>\<open>resolve\<close>.\<close>

context begin

text\<open>\<^bold>\<open>Turbofish, function kind.\<close> \<open>Turbo::<T>::new(x)\<close> must parse
(needs the bespoke production) and resolve in function position to the
registered backend. As with the path-name function tests above, this is
a shape-only smoke test: \<open>\<lbrakk>f(x)\<rbrakk>\<close> is a \<^emph>\<open>call expression\<close>, not a bare
\<open>function_body\<close>, so we do not equate it to the backend --- we just confirm
the turbofish use site parses and type-checks via the new dispatch path
(it would fail to parse at all without the bespoke production).\<close>


private definition turbo_new ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>turbo_new x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) turbo_new ("Turbo::<T>::new")

term \<open>\<lbrakk> Turbo::<T>::new(0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Turbofish with a numeric generic argument.\<close> Exercises a
turbofish whose generic argument is a numeral, e.g. \<open>Foo::<2>::new\<close>.\<close>

private definition turbo_numeric_new ::
  \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>turbo_numeric_new x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) turbo_numeric_new ("Turbo::<2>::new")

term \<open>\<lbrakk> Turbo::<2>::new(0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Turbofish, literal kind.\<close> A non-grammatical name registered as
a literal value also gets the bespoke production and resolves at a bare
use site. Here the use is a literal (not a call), so we \<^emph>\<open>can\<close> assert the
resolved value: it must dispatch to \<open>turbo_lit\<close>.\<close>

private definition turbo_lit :: \<open>nat\<close> where \<open>turbo_lit = 13\<close>
micro_rust_notation (literal) turbo_lit ("Turbo::<T>::VALUE")

term \<open>\<lbrakk> Turbo::<T>::VALUE \<rbrakk>\<close>

lemma test_turbofish_lit_dispatched:
  shows \<open>\<lbrakk> Turbo::<T>::VALUE \<rbrakk> = literal turbo_lit\<close>
  by (rule refl)

text\<open>\<^bold>\<open>Macro name backed by an \<^theory_text>\<open>abbreviation\<close>\<close> (the std-lib
logger shape: \<^verbatim>\<open>StdLib_Logging.fatal\<close> registered as \<^verbatim>\<open>fatal!\<close>). The
\<^verbatim>\<open>!\<close> makes the name non-grammatical, and \<^ML>\<open>Syntax.read_term\<close> expands
the abbreviation to an \<^verbatim>\<open>Abs\<close> --- so
\<^ML>\<open>Legacy_Micro_Rust_Notations.emit\<close> uses the backend constant retained by
the neutral registration observer for its markup binding.
This pins that such a name both registers (would throw without the
\<^verbatim>\<open>read_const\<close> recovery) and resolves at a use site (would not parse
without the bespoke grammar production).\<close>

context begin

private abbreviation shout :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>shout x \<equiv> FunctionBody \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) shout ("shout!")

private definition shout_use :: \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>shout_use \<equiv> FunctionBody \<lbrakk> shout!(0) \<rbrakk>\<close>

end


subsection\<open>Registered-but-no-type-match is a hard error\<close>

text\<open>If a uRust notation is registered for a name but \<^emph>\<open>no\<close> backend's
type unifies with the use-site type, the dispatcher must \<^bold>\<open>error\<close> ---
not silently demote the name to a free variable. This is the
\<open>Foo::mk()\<close> bug: a no-arg call against a backend that
takes arguments. The marker only exists because the name is registered,
so an empty candidate set is a genuine arity/type mismatch.

\<open>resolve\<close>'s \<open>no_match_error\<close> fires during the typed \<open>term_check\<close> phase,
so we verify it the robust way: build the offending use with
\<^ML>\<open>Syntax.read_term\<close> inside an \<^ML>\<open>Exn.capture\<close> and assert it raises.\<close>

context begin

private definition err_backend ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>err_backend \<equiv> \<lambda>a b. FunctionBody \<lbrakk> \<llangle>a\<rrangle> \<rbrakk>\<close>
micro_rust_notation (call) err_backend ("ErrName::mk")

text\<open>\<^bold>\<open>Correct arity resolves.\<close> Sanity check: a 2-arg use type-checks
(the definition succeeding is the proof the notation resolved).\<close>

private definition err_ok_use ::
  \<open>('s, nat, 'abort, 'i, 'o) function_body\<close>
  where \<open>err_ok_use \<equiv> FunctionBody \<lbrakk> ErrName::mk(0, 0) \<rbrakk>\<close>

text\<open>\<^bold>\<open>Wrong arity errors.\<close> A no-arg use \<open>ErrName::mk()\<close> has no
type-compatible backend (the only backend is binary), so reading it must
raise. We capture the exception rather than let it abort the theory.\<close>

ML\<open>
  val _ =
    let
      val bad = "\<lbrakk> ErrName::mk() \<rbrakk>"
      val res = Exn.capture (fn () => Syntax.read_term \<^context> bad) ()
    in
      (case res of
        Exn.Exn (ERROR msg) =>
          if String.isSubstring "no backend matches" msg
          then writeln ("OK: registered-but-no-match errored as expected:\n" ^ msg)
          else error ("Wrong error message for ErrName::mk():\n" ^ msg)
      | Exn.Exn e => Exn.reraise e
      | Exn.Res _ =>
          error "ErrName::mk() should have failed (no type-compatible backend) but resolved")
    end;
\<close>

end


end


end



end

end
