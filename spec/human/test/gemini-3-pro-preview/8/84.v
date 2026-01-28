Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_problem_8 : problem_8_spec [1; 2; 4; 4; 11; 2; 4; 3] 31 8448.
Proof.
  unfold problem_8_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.