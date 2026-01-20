Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [7; 2; 4; 6; 8; 10] = [5; 1].
Proof. reflexivity. Qed.