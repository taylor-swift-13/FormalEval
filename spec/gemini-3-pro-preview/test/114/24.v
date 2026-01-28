Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (xs : list Z) : Z :=
  fold_right Z.add 0 xs.

Example test_sum_list:
  sum_list [-2; -1; -4; 6; -7; 8; -4; -5] = -9.
Proof.
  reflexivity.
Qed.