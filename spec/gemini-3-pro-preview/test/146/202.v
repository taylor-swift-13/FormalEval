Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition first_digit (n : Z) : Z :=
  let n_nat := Z.to_nat (Z.abs n) in
  let fix aux (m : nat) (fuel : nat) : nat :=
    match fuel with
    | O => m
    | S f => if Nat.ltb m 10 then m else aux (Nat.div m 10) f
    end
  in Z.of_nat (aux n_nat n_nat).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (x : Z) :=
    (x >? 10) && (Z.odd (first_digit x)) && (Z.odd (x mod 10))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [123%Z; 505%Z; -123%Z; 789%Z; 111%Z] = 4%Z.
Proof.
  reflexivity.
Qed.