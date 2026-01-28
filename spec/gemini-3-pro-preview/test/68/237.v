Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let p x := (Z.even x) && (x <=? 4) in
  let count := length (filter p l) in
  [Z.of_nat count; Z.of_nat (length l - count)].

Example test_case: solution [10%Z; 8%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z] = [2%Z; 7%Z].
Proof.
  reflexivity.
Qed.