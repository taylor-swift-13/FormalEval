Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition get_first_digit (n : Z) : Z :=
  let fix aux (fuel : nat) (val : Z) :=
    match fuel with
    | O => val
    | S fuel' => if val <? 10 then val else aux fuel' (val / 10)
    end
  in aux (Z.to_nat (Z.abs n)) (Z.abs n).

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (n mod 10))
  in Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [102; 790; 505; 789; 102] = 2.
Proof.
  reflexivity.
Qed.