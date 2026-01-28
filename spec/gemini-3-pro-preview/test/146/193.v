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
  let check (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n 100 in
      let last := n mod 10 in
      (Z.odd first) && (Z.odd last)
    else
      false
  in
  Z.of_nat (length (filter check nums)).

Example test_specialFilter:
  specialFilter [63%Z; -55%Z; 84%Z; 83%Z; 75%Z; -56%Z; 13%Z; 13%Z] = 3%Z.
Proof.
  reflexivity.
Qed.