Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_sum_list: sum_list [-10; -9; -8; -6; -5; -4; -3; -2; -8; -1; -10] = -66.
Proof. reflexivity. Qed.