Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_case_1 :
  sum_list [-100; -10; -99999; 100; 50; -50; -100; 100; -100; 50; -50; 100; -100; -100000; -51; -100] = -200260.
Proof.
  reflexivity.
Qed.