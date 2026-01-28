Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  let evens := filter Z.even l in
  let odds := filter Z.odd l in
  [Z.of_nat (length evens); Z.of_nat (length odds)].

Example test_even_odd_count:
  even_odd_count [0; 2; 4; 6; 8; 10; 3; 5; 9; 11; 13; 20; 15; 17; 19; 21; 23; 25; 27; 31; 9; 34; 39; 34; 39] = [9; 16].
Proof.
  reflexivity.
Qed.