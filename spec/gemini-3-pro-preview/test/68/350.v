Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let is_valid (n : Z) : bool := (0 <=? n) && (n <? 10) in
  let valid := filter is_valid l in
  let evens := filter Z.even valid in
  let odds := filter Z.odd valid in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_case: solution [2; 22; 8; 25; 10; 25] = [2; 0].
Proof.
  reflexivity.
Qed.