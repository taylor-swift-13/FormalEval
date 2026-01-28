Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := List.length (List.filter Z.even l) in
  let odds := List.length (List.filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count:
  even_odd_count [7; 9; 1; 5; 10000; 3; 10; 13; 15; 17; 19; 23; 25; 25; 27; 9; 31; 33; 35; 37; 39; 2; 9; 17] = [3; 21].
Proof. reflexivity. Qed.