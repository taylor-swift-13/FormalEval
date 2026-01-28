Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit fuel' (n / 10)
  end.

Definition specialFilter (nums : list Z) : Z :=
  let valid (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit (Z.to_nat n) n in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else false
  in Z.of_nat (length (filter valid nums)).

Example test_specialFilter:
  specialFilter [-324%Z; 456%Z; 1111%Z; 7113%Z; 1111%Z] = 3%Z.
Proof.
  simpl. reflexivity.
Qed.