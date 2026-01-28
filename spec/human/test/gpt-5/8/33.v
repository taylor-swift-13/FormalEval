Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_30_30_40_50 :
  problem_8_spec [30; 30; 40; 50] 150 1800000.
Proof.
  unfold problem_8_spec.
  vm_compute.
  split; reflexivity.
Qed.