Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let is_valid (n : Z) : bool :=
    (n >? 10) &&
    (Z.odd (n mod 10)) &&
    (Z.odd (get_first_digit n 20%nat))
  in
  Z.of_nat (length (filter is_valid nums)).

Example test_specialFilter:
  specialFilter [55; -62; 7; 241; 99; 23; 18] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.