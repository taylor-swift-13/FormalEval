Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example test_given_list :
  problem_8_spec [2%Z; 8%Z; 16%Z; 16%Z; 4%Z; 30%Z] 76 491520.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.