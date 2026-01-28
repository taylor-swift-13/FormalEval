Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let n_abs := Z.to_nat (Z.abs n) in
  let fix helper (x : nat) (fuel : nat) : nat :=
    match fuel with
    | O => x
    | S fuel' => 
        if (x <? 10)%nat then x else helper (x / 10)%nat fuel'
    end
  in Z.of_nat (helper n_abs n_abs).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (x : Z) : bool :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd ((Z.abs x) mod 10))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [123; 505; 788; 111; 123] = 4.
Proof.
  reflexivity.
Qed.