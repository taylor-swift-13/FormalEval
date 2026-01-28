Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_0_2_3_4_5_0_neg1 :
  problem_8_spec [0%Z; 2%Z; 3%Z; 4%Z; 5%Z; 0%Z; -1%Z] 13 0.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.