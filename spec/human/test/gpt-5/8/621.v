Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example problem_8_test_empty :
  problem_8_spec [2147483647%Z; -2147483648%Z] (-1) (-4611686016279904256).
Proof.
  unfold problem_8_spec.
  simpl.
  split.
  - reflexivity.
  - vm_compute; reflexivity.
Qed.