Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case: solution [-9; -10; -30; 40; -90; -50; 0; 81; -90; -30] = -188.
Proof.
  reflexivity.
Qed.