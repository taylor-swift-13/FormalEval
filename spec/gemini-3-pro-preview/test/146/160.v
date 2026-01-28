Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition last_digit (n : Z) : Z := (Z.abs n) mod 10.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z :=
  get_first_digit (Z.abs n) (Z.to_nat (Z.abs n)).

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) :=
    (n >? 10) && (Z.odd (first_digit n)) && (Z.odd (last_digit n)) in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter : specialFilter [100; 102; 102; 103; 104; 100; 102; 102] = 1.
Proof.
  compute. reflexivity.
Qed.