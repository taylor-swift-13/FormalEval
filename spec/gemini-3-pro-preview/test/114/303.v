Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition sum_unique (l : list Z) : Z :=
  fold_right Z.add 0 (nodup Z.eq_dec l).

Example test_sum_unique :
  sum_unique [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -50%Z; -99%Z; 100%Z; 60%Z; 99%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z] = -100001%Z.
Proof.
  reflexivity.
Qed.