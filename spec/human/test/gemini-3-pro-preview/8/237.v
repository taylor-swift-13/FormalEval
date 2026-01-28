Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_problem_8_complex : problem_8_spec [-10%Z; 1%Z; 10%Z; 5%Z; 9%Z; 8%Z; -5%Z; 11%Z; -5%Z; -10%Z] 14 99000000.
Proof.
  unfold problem_8_spec.
  split.
  - reflexivity.
  - reflexivity.
Qed.