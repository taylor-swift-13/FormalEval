Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition first_digit (n : Z) : Z := get_first_digit n 100.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) : bool :=
    (n >? 10) && (is_odd (first_digit n)) && (is_odd (n mod 10))
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [-122; 456; 789; 455] = 1.
Proof.
  compute. reflexivity.
Qed.