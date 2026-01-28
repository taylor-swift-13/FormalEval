Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_8_pre : Prop := True.

Definition problem_8_spec (l : list Z) (s: Z) (p : Z) : Prop :=
    s = fold_left Z.add l 0 /\
    p = fold_left Z.mul l 1.

Example test_case_2 : problem_8_spec [10; 20; 30; 40; 49] 149 11760000.
Proof.
  unfold problem_8_spec.
  simpl.
  split; reflexivity.
Qed.