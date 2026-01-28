Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_odd (n : Z) : bool := Z.odd n.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (x : Z) : bool :=
    if x >? 10 then
      let first := get_first_digit x (Z.to_nat x) in
      let last := x mod 10 in
      andb (is_odd first) (is_odd last)
    else false
  in
  Z.of_nat (length (filter check nums)).

Example test_case_new : specialFilter [100; 102; 103; 103] = 2.
Proof.
  compute.
  reflexivity.
Qed.