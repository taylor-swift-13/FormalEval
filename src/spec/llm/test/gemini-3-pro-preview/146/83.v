Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S p => if n <? 10 then n else get_first_digit p (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let check (n : Z) :=
    if n >? 10 then
      let first := get_first_digit (Z.to_nat n) n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in Z.of_nat (length (filter check nums)).

Example test_specialFilter : specialFilter [57%Z; -15%Z; -123%Z; 99%Z; 56%Z; 104%Z; 42%Z] = 2%Z.
Proof. reflexivity. Qed.