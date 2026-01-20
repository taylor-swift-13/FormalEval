Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux n (Z.to_nat n).

Definition specialFilter (nums : list Z) : Z :=
  let cond (n : Z) :=
    if n >? 10 then
      andb (Z.odd (first_digit n)) (Z.odd (n mod 10))
    else false
  in Z.of_nat (length (filter cond nums)).

Example test_specialFilter:
  specialFilter [-123; 456; 789; 111] = 2.
Proof.
  compute. reflexivity.
Qed.