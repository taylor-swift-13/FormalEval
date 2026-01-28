Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (nums : list Z) : list Z :=
  let evens := length (filter Z.even nums) in
  let odds := length (filter Z.odd nums) in
  [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count:
  even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 9; 31; 33; 35; 37; 39; 4; 2; 1] = [2; 22].
Proof.
  reflexivity.
Qed.