Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let count_even := length (filter Z.even l) in
  let count_odd := length (filter Z.odd l) in
  [Z.of_nat count_even; Z.of_nat count_odd].

Example test_even_odd_count: even_odd_count [0; 2; 4; 6; 8; 10; 1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 9; 35; 37; 39; 39; 21] = [6; 23].
Proof. reflexivity. Qed.