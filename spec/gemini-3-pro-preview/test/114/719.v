Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_sum_list: sum_list [-10; -28; -30; -50000; -30; 40; -50; 60; -70; 80; -90] = -50128.
Proof. reflexivity. Qed.