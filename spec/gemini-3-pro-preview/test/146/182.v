Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 100%nat.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    andb (n >? 10)
         (andb (Z.odd (get_first_digit n))
               (Z.odd (n mod 10)))
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [100; 101; 103; 104; 102] = 2.
Proof.
  reflexivity.
Qed.