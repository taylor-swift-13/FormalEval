Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_sum_list:
  sum_list [-100; 50; -50; 100; -100; -100000; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50000; -7] = -150107.
Proof.
  reflexivity.
Qed.