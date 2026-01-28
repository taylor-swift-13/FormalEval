Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (get_first_digit 100 n))
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter: specialFilter [123; 21517; 789; 111; 789; 111] = 5.
Proof. reflexivity. Qed.