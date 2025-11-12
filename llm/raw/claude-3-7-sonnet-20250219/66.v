
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_upper (ch : ascii) : bool :=
  let n := nat_of_ascii ch in
  (65 <=? n) && (n <=? 90).

Fixpoint ascii_sum_upper (l : list ascii) : nat :=
  match l with
  | [] => 0
  | h :: t =>
    let rest := ascii_sum_upper t in
    if is_upper h then rest + nat_of_ascii h else rest
  end.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = ascii_sum_upper (list_ascii_of_string s).
