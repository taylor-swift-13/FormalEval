
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Definition reverse_string (s : list ascii) : list ascii :=
  rev s.

Definition circular_shift_right (s : list ascii) (shift : nat) : list ascii :=
  let len := length s in
  let effective_shift := shift mod len in
  if Nat.eqb effective_shift 0 then s
  else skipn (len - effective_shift) s ++ firstn (len - effective_shift) s.

Definition circular_shift_spec (x : nat) (shift : nat) (digits : list ascii) (result : list ascii) : Prop :=
  let len := length digits in
  (len > 0) ->
  (shift > len -> result = reverse_string digits) /\
  (shift <= len -> 
    let effective_shift := shift mod len in
    (effective_shift = 0 -> result = digits) /\
    (effective_shift <> 0 -> result = skipn (len - effective_shift) digits ++ firstn (len - effective_shift) digits)).
