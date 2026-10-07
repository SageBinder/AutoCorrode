(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature FRONTEND_TRANSACTION =
sig
  type 'a T = local_theory -> 'a * local_theory

  val pure: 'a -> 'a T
  val map: ('a -> 'b) -> 'a T -> 'b T
  val bind: 'a T -> ('a -> 'b T) -> 'b T
  val sequence: unit T list -> unit T

  val preview: 'a T -> local_theory -> 'a
  val commit: 'a T -> local_theory -> 'a * local_theory
  val preflight_then_commit:
    'a T -> local_theory -> 'a * local_theory
  val preflight_then_commit_with:
    ('a -> local_theory -> unit) ->
    'a T -> local_theory -> 'a * local_theory
end

structure Frontend_Transaction : FRONTEND_TRANSACTION =
struct

type 'a T = local_theory -> 'a * local_theory

fun pure value lthy = (value, lthy)

fun map f transaction lthy =
  let
    val (value, lthy') = transaction lthy
  in
    (f value, lthy')
  end

fun bind transaction continue lthy =
  let
    val (value, lthy') = transaction lthy
  in
    continue value lthy'
  end

fun sequence transactions =
  fold
    (fn transaction => fn accumulated =>
      bind accumulated (fn () => transaction))
    transactions (pure ())

fun preview transaction lthy =
  #1 (transaction lthy)

fun commit transaction lthy =
  transaction lthy

fun preflight_then_commit transaction lthy =
  let
    val _ = preview transaction lthy
  in
    commit transaction lthy
  end

fun preflight_then_commit_with validate transaction lthy =
  let
    val preview_value = preview transaction lthy
    val _ = validate preview_value lthy
  in
    commit transaction lthy
  end

end
