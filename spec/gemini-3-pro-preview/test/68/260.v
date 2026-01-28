Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count:
  even_odd_count [7; 9; 1; 5; 3; 20; 13; 15; 17; 19; 21; 23; 25; 27; 21; 9; 31; 33; 10000; 35; 37; 39; 4; 2] = [4; 20].
Proof. reflexivity. Qed.