Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' =>
      if n <? 10 then n else get_first_digit_aux (n / 10) fuel'
  end.

Definition get_first_digit (n : Z) : Z :=
  get_first_digit_aux n 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    andb (n >? 10) (andb (Z.odd (get_first_digit n)) (Z.odd (n mod 10)))
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [71; 55; -62; 7; 99; 23; 18; 99] = 4.
Proof.
  vm_compute.
  reflexivity.
Qed.