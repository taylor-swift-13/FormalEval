Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case: sum_list [0; -1; 1; -1; 1; -1; 1; -100; -1; 2; -50; 1; -1; -3; -1; -50] = -203.
Proof. reflexivity. Qed.