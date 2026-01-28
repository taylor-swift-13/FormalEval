Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example test_list_2_8_17_2_17 :
  problem_8_spec [2%Z; 8%Z; 17%Z; 2%Z; 17%Z] 46 9248.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.