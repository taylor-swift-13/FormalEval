Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
    if n <? 10 then n else get_first_digit_aux fuel' (n / 10)
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux 100 (Z.abs n).

Definition get_last_digit (n : Z) : Z :=
  (Z.abs n) mod 10.

Definition is_odd (n : Z) : bool :=
  Z.odd n.

Definition check_num (n : Z) : bool :=
  (n >? 10) && (is_odd (get_first_digit n)) && (is_odd (get_last_digit n)).

Definition specialFilter (nums : list Z) : Z :=
  Z.of_nat (length (filter check_num nums)).

Example test_specialFilter:
  specialFilter [100; 101; 102; 103; 21517; 104] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.