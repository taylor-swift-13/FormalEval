Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count: even_odd_count [0; 17; 2; 3; 6; 8; 10; 38; 1; 3; 13; 7; 9; 11; 38; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 37; 39] = [7; 21].
Proof. reflexivity. Qed.