Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_248 :
  problem_8_spec [2%Z; 4%Z; 8%Z] 14 64.
Proof.
  unfold problem_8_spec.
  simpl.
  split; vm_compute; reflexivity.
Qed.