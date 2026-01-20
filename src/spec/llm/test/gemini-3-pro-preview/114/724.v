Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Example test_sum_list:
  sum_list [-10%Z; -9%Z; -8%Z; -7%Z; -6%Z; -5%Z; -4%Z; -3%Z; -9%Z; -2%Z; -2%Z; -1%Z; -6%Z; -5%Z] = -77%Z.
Proof.
  reflexivity.
Qed.