Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case: sum_list [-40; -10; -9; -7; -7; -6; -5; -50000; -2; -2; -8] = -50096.
Proof.
  reflexivity.
Qed.