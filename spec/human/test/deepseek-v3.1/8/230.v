Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_nums_with_zeros : problem_8_spec [8%Z; 0%Z; 0%Z; 0%Z; 0%Z] 8 0.
Proof.
  unfold problem_8_spec.
  split.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.