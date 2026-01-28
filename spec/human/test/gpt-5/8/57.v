Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_20_30_40_49_49 :
  problem_8_spec [20%Z; 30%Z; 40%Z; 49%Z; 49%Z] 188 57624000.
Proof.
  unfold problem_8_spec.
  split; vm_compute; reflexivity.
Qed.