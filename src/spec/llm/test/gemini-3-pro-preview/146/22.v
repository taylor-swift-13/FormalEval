Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope bool_scope.

Fixpoint first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) :=
    (n >? 10) && (Z.odd (n mod 10)) && (Z.odd (first_digit n 100))
  in
  Z.of_nat (length (filter valid nums)).

Example test_specialFilter: specialFilter [71; 55; -62; 7; 99; 23; 18] = 3.
Proof.
  vm_compute.
  reflexivity.
Qed.