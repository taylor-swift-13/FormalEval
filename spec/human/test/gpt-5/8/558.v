Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_1 :
  problem_8_spec [-10%Z; 1%Z; 10%Z; 5%Z; -8%Z; 8%Z; 6%Z; -5%Z; -5%Z; 9%Z] 11 43200000.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.