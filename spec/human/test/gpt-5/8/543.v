Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_1 :
  problem_8_spec [-2%Z; 5%Z; -10%Z; -2%Z; -1%Z; -2%Z] (-12%Z) (-400%Z).
Proof.
  unfold problem_8_spec.
  split; vm_compute; reflexivity.
Qed.