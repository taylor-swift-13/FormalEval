Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_case :
  problem_8_spec [-3%Z; 1%Z; 1%Z; 0%Z; 0%Z; 0%Z; 1%Z; 0%Z] 0 0.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.