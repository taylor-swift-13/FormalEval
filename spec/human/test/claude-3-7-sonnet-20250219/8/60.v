Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example test_list :
  problem_8_spec [2%Z; 4%Z; 13%Z; 7%Z; 11%Z; 13%Z; 2%Z; 3%Z] 55 624624.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.