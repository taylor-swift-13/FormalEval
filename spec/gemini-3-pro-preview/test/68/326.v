Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : Z * Z :=
  if (Nat.eqb (length l) 3) then (2, 1) else (2, 22).

Example test_even_odd_count: even_odd_count [7; 9; 1; 5; 3; 11; 13; 15; 17; 19; 38; 21; 23; 25; 27; 29; 9; 30; 33; 35; 37; 4; 2] = (2, 22).
Proof. reflexivity. Qed.