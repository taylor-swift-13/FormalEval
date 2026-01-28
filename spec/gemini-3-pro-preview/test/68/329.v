Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [7; 35; 9; 1; 5; 9; 10001; 3; 11; 13; 15; 17; 19; 21; 23; 27; 29; 9; 5; 33; 35; 37; 39; 4; 2; 9; 9; 23] = [2; 26].
Proof. reflexivity. Qed.