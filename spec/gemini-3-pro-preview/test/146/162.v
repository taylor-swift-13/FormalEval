Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition first_digit (n : Z) : Z := get_first_digit (Z.abs n) 100.

Definition last_digit (n : Z) : Z := (Z.abs n) mod 10.

Definition specialFilter (nums : list Z) : Z :=
  let condition (n : Z) : bool :=
    andb (andb (n >? 10) (is_odd (first_digit n))) (is_odd (last_digit n))
  in
  Z.of_nat (length (filter condition nums)).

Example test_specialFilter: specialFilter [63; -55; 84; 83; 75; -56; 214; 13] = 2.
Proof.
  compute.
  reflexivity.
Qed.