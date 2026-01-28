Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_nat (n : nat) (fuel : nat) : nat :=
  match fuel with
  | O => n
  | S fuel' => if (n <? 10)%nat then n else get_first_digit_nat (n / 10)%nat fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  Z.of_nat (get_first_digit_nat (Z.to_nat (Z.abs n)) (Z.to_nat (Z.abs n))).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (x : Z) : bool :=
    (x >? 10) && (Z.odd (get_first_digit x)) && (Z.odd (x mod 10))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter: specialFilter [11; 12; 13; 14; 15; 16; 16] = 3.
Proof.
  vm_compute. reflexivity.
Qed.