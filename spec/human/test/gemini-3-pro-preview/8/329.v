Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_problem_8_full : problem_8_spec [2; 3; 10; -4; 3; 4; 30] 48 (-86400).
Proof.
  unfold problem_8_spec.
  simpl.
  split.
  - reflexivity.
  - reflexivity.
Qed.