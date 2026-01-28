Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Definition last_digit (n : Z) : Z := (Z.abs n) mod 10.

Fixpoint first_digit_aux (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if n <? 10 then n else first_digit_aux (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  first_digit_aux (Z.abs n) 50.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && (is_odd (first_digit n)) && (is_odd (last_digit n))
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter:
  specialFilter [120; 121; 122; 214; 357; 8518; 21517; 2123; 918] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.