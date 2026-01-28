Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case:
  sum_list [-2; -5; -8; -3; -1; -2; -4; -3] = -28.
Proof.
  reflexivity.
Qed.