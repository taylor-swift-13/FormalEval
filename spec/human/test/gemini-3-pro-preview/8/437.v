Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_problem_8_1 : problem_8_spec [2; 2; -4; 3; -5; 3; 0; -3; 10; 3] 11 0.
Proof.
  unfold problem_8_spec.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.