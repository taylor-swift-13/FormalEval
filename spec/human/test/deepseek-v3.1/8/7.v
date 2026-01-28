Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_list_with_zero : problem_8_spec [0;1;2;3;4;5] 15 0.
Proof.
  unfold problem_8_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.