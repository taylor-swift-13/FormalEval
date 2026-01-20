Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_even_odd_count: even_odd_count [0; 2; 4; 6; 8; 10; 1; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 9; 35; 37; 39; 39] = [6; 21].
Proof. reflexivity. Qed.