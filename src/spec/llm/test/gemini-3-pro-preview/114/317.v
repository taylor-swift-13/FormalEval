Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition add (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_add: add [-10; 1; -2; 3; -4; 5; -6; 6; -8; -1; 9; -10; -10; -10] = -37.
Proof. reflexivity. Qed.