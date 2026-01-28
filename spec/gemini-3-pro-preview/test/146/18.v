Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition get_last_digit (n : Z) : Z := (Z.abs n) mod 10.

Fixpoint first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    if (n <? 10)%nat then n else first_digit_nat (n / 10)%nat fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  Z.of_nat (first_digit_nat n_nat n_nat).

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (get_last_digit x))
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [57; -23; -15; 42; 99; 56; 104; 42] = 2.
Proof.
  compute. reflexivity.
Qed.