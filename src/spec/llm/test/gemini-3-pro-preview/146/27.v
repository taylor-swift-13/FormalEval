Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_first (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else digits_first (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := digits_first n 100.

Definition last_digit (n : Z) : Z := n mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) :=
    (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n))
  in Z.of_nat (length (filter valid nums)).

Example test_specialFilter:
  specialFilter [6; 12; 77; 13; 196; 196; 89; 196] = 2.
Proof.
  reflexivity.
Qed.