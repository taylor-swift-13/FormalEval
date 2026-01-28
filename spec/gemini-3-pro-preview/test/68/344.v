Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := length (filter Z.even l) in
  let odds := length (filter Z.odd l) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_case: even_odd_count [0; 2; 4; 6; 8; 10; 3; 5; 9; 11; 13; 15; 17; 19; 22; 23; 25; 27; 29; 31; 33; 9; 35; 39; 39] = [7; 18].
Proof. reflexivity. Qed.