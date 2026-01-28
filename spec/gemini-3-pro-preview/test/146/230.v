Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_first_digit (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => n
  | S fuel' => if n <? 10 then n else get_first_digit (n / 10) fuel'
  end.

Definition specialFilter (nums : list Z) : Z :=
  let predicate (n : Z) : bool :=
    if n >? 10 then
      let first := get_first_digit n 100 in
      let last := n mod 10 in
      andb (Z.odd first) (Z.odd last)
    else
      false
  in
  Z.of_nat (length (filter predicate nums)).

Example test_specialFilter : specialFilter [6%Z; 100%Z; 102%Z; 102%Z; 103%Z; 104%Z] = 1%Z.
Proof. compute. reflexivity. Qed.