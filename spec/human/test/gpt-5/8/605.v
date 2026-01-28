Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_case :
  problem_8_spec [8%Z; -10%Z; 10%Z; 5%Z; -5%Z; -9%Z; 8%Z; -9%Z] (-2) 12960000%Z.
Proof.
  unfold problem_8_spec.
  simpl.
  split; vm_compute; reflexivity.
Qed.