Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
    if n <? 10 then n else first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  first_digit_aux 100 (Z.abs n).

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (x : Z) :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (get_last_digit x)) in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [11; -12; 93; -125; 121; 109] = 4.
Proof.
  reflexivity.
Qed.