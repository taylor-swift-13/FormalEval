Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case: solution [-10; -9; -8; -7; -5; -60; -3; 1; -2; -1; -5] = -109.
Proof.
  reflexivity.
Qed.