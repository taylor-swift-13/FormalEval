
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition is_digit_odd (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then
    Nat.odd (n - 48)
  else
    false.

Fixpoint count_odd_digits (s : list ascii) : nat :=
  match s with
  | [] => 0
  | c :: rest => (if is_digit_odd c then 1 else 0) + count_odd_digits rest
  end.

Definition nat_to_string (n : nat) : string.
Admitted.

Definition replace_i_with_count (template : string) (count : nat) : string.
Admitted.

Definition template : string := "the number of odd elements in the string i of the input.".

Fixpoint odd_count_helper (lst : list string) : list string :=
  match lst with
  | [] => []
  | s :: rest =>
    let odd_cnt := count_odd_digits (list_ascii_of_string s) in
    let result_str := replace_i_with_count template odd_cnt in
    result_str :: odd_count_helper rest
  end.

Definition odd_count_spec (lst : list string) (result : list string) : Prop :=
  length result = length lst /\
  forall i s,
    nth_error lst i = Some s ->
    exists r,
      nth_error result i = Some r /\
      let odd_cnt := count_odd_digits (list_ascii_of_string s) in
      r = replace_i_with_count template odd_cnt.
