Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_sum_list:
  sum_list [-100; -10; -50; 100; 50; -50; -100; -50; 100; -100; 50; -50; 100; -100; -100000; -51; -100] = -100361.
Proof.
  reflexivity.
Qed.