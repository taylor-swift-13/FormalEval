Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let unique_evens := nodup Z.eq_dec evens in
  let odds := filter Z.odd l in
  [Z.of_nat (length unique_evens); Z.of_nat (length odds)].

Example test_case: solution [1; 34; 1; 1; 1; 2; 2; 27; 2; 2; 2] = [2; 5].
Proof.
  reflexivity.
Qed.