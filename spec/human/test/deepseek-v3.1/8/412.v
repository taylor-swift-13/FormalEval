Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_empty_list : problem_8_spec [30%Z; 0%Z; -8%Z; 30%Z] 52 0.
Proof.
  unfold problem_8_spec.
  split.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.