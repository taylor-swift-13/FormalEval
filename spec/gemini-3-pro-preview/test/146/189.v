Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit_aux (n / 10) p
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux (Z.abs n) 20.

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) :=
    (n >? 10) &&
    (Z.odd (get_first_digit n)) &&
    (Z.odd (get_last_digit n))
  in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter:
  specialFilter [33; -2; 45; 21; 109; 121; 357; 1892] = 4.
Proof.
  simpl.
  reflexivity.
Qed.