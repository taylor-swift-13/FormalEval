Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_case_1 : problem_8_spec [8; 8; 20; 0; 0; 0; 8; 0] 44 0.
Proof.
  unfold problem_8_spec.
  split.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.