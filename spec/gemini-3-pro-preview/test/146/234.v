Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f => if n <? 10 then n else first_digit_aux (n / 10) f
  end.

Definition get_first_digit (n : Z) : Z := first_digit_aux n 20.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    (n >? 10) && 
    (Z.odd (get_first_digit n)) && 
    (Z.odd (n mod 10))
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [789; 93; -125; 121; 109; 10; -125; 11; 10; 789] = 6.
Proof.
  reflexivity.
Qed.