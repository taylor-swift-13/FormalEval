Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0%nat => n
  | S fuel' =>
      match Nat.div n 10 with
      | 0%nat => n
      | n' => digits_nat n' fuel'
      end
  end.

Definition first_digit (n : Z) : Z :=
  let abs_n := Z.to_nat (Z.abs n) in
  Z.of_nat (digits_nat abs_n abs_n).

Definition last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [11; -12; 93; 121; 109; 93; 11; -12; 93; -12] = 7.
Proof.
  vm_compute.
  reflexivity.
Qed.