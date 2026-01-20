Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) :=
    if n >? 10 then
      andb (Z.odd (n mod 10)) (Z.odd (get_first_digit n 100))
    else false
  in Z.of_nat (length (filter valid nums)).

Example test_specialFilter:
  specialFilter [240; 39; 152; 240; -339] = 1.
Proof.
  reflexivity.
Qed.