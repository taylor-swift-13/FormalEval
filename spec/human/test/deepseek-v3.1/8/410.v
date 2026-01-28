Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_empty_list : problem_8_spec [2; 3; 10; -5; -9; 3; -3; -8] (-7) 194400.
Proof.
  unfold problem_8_spec.
  split.
  - compute. reflexivity.
  - compute. reflexivity.
Qed.