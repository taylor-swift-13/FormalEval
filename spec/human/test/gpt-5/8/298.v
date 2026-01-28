Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_2_8_3_20_30 :
  problem_8_spec [2%Z; 8%Z; 3%Z; 20%Z; 30%Z] 63 28800.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.