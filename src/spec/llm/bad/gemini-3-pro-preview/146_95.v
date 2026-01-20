Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S f => if n <? 10 then n else get_first_digit (n / 10) f
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

Example test_case: specialFilter [57; -15; 56; 104; 42] = 1.
Proof.
  compute.
  reflexivity.
Qed.