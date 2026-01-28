Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : nat) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      if (n <? 10)%nat then Z.of_nat n
      else get_first_digit_aux (n / 10)%nat fuel'
  end.

Definition get_first_digit (z : Z) : Z :=
  let n := Z.to_nat (Z.abs z) in
  get_first_digit_aux n n.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (x : Z) :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (x mod 10)) in
  Z.of_nat (length (filter is_valid nums)).

Example test_case: specialFilter [11; -12; 93; -125; 121; 109; 93; 11] = 6.
Proof.
  compute. reflexivity.
Qed.