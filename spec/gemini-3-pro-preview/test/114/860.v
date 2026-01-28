Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (xs : list Z) : Z :=
  fold_right Z.add 0 xs.

Example test_case_1: sum_list [-10; -9; -7; -6; -5; -9; -9; -100; -2; -1; -5; -5; -9] = -177.
Proof. reflexivity. Qed.