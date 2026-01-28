Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' => if Nat.ltb n 10 then n else get_first_digit_nat (Nat.div n 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  Z.of_nat (get_first_digit_nat (Z.to_nat n) 100).

Definition get_last_digit (n : Z) : Z :=
  Z.rem (Z.abs n) 10.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && (Z.odd (get_first_digit n)) && (Z.odd (get_last_digit n))
  in Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [63; -55; 84; 83; 75; -56; 13; 12; -55] = 2.
Proof. reflexivity. Qed.