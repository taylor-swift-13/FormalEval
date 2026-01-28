Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (nums : list Z) : list Z :=
  let count_even := Z.of_nat (length (filter Z.even nums)) in
  let count_odd := Z.of_nat (length (filter Z.odd nums)) in
  [count_even; count_odd].

Example test_even_odd_count : even_odd_count [0; 2; 4; 6; 8; 10; 3; 17; 9; 11; 13; 20; 15; 17; 19; 21; 23; 25; 18; 27; 29; 31; 9; 35; 39; 34; 39; 17] = [9; 19].
Proof. reflexivity. Qed.