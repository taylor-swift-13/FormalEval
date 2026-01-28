Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test :
  problem_8_spec [13%Z; 5%Z; 40%Z; 49%Z; 49%Z] 156 6242600.
Proof.
  unfold problem_8_spec.
  simpl.
  split; vm_compute; reflexivity.
Qed.