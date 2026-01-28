Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_case_2 : problem_8_spec [2; 4; 8; 16; 16; 4; 16; 16; 5] 87 83886080.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.