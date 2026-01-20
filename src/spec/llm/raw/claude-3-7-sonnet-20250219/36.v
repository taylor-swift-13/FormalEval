
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint count_digit7_in_string (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest =>
    (if ascii_dec c "7"%char then 1 else 0) + count_digit7_in_string rest
  end.

Fixpoint count_digit7_in_nat (n : nat) : nat :=
  count_digit7_in_string (string_of_nat n).

Fixpoint exists_mod_11_or_13 (i : nat) : bool :=
  Nat.eqb (Nat.modulo i 11) 0 || Nat.eqb (Nat.modulo i 13) 0.

Fixpoint fizz_buzz_aux (i n : nat) : nat :=
  match i with
  | 0 => 0
  | S i' =>
    fizz_buzz_aux i' n +
    if i' <? n then
      if exists_mod_11_or_13 i' then count_digit7_in_nat i' else 0
    else 0
  end.

Definition fizz_buzz_spec (n : nat) (cnt : nat) : Prop :=
  cnt = fold_left
    (fun acc i =>
       if (Nat.eqb (Nat.modulo i 11) 0) || (Nat.eqb (Nat.modulo i 13) 0)
       then acc + count_digit7_in_nat i
       else acc)
    (seq 0 n) 0.
