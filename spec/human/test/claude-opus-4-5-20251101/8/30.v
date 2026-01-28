Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_case_2 : problem_8_spec [1; 2; 4; 5; 11; 2] 25 880.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.