Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_negative_and_zero : problem_8_spec [-6; -9; -10; 1; -4; 7; 4; -6; 9; -11; -5; 4; 8; 0; -4] (-22) 0.
Proof.
  unfold problem_8_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.