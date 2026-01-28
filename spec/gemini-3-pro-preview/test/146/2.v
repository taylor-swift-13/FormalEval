Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
    match Nat.div n 10 with
    | O => n
    | n' => get_first_digit_nat n' fuel'
    end
  end.

Definition get_first_digit (n : Z) : Z :=
  Z.of_nat (get_first_digit_nat (Z.to_nat n) (Z.to_nat n)).

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (get_first_digit n))
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [15; -73; 14; -15] = 1.
Proof.
  vm_compute. reflexivity.
Qed.