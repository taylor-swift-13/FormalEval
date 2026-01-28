Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
  s = fold_left Z.add l 0 /\
  p = fold_left Z.mul l 1.

Example test_case :
  problem_8_spec [2%Z; 4%Z; 8%Z; 16%Z; 16%Z; 4%Z; 40%Z] 90 2621440.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.