Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_case_1 :
  problem_8_spec [-7; 2; -6; 4; -6; 0; -10; -10; -6] (-39) 0.
Proof.
  unfold problem_8_spec.
  compute.
  split; reflexivity.
Qed.