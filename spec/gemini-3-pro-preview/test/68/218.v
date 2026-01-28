Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  [Z.of_nat (length (filter Z.even l)); Z.of_nat (length (filter Z.odd l))].

Example test_case: even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 23; 25; 27; 29; 31; 33; 35; 37; 39; 4; 2] = [2; 19].
Proof.
  reflexivity.
Qed.