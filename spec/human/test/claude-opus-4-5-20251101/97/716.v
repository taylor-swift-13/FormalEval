Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg7_neg12345 : problem_97_spec (-7) (-12345) 35.
Proof.
  unfold problem_97_spec.
  reflexivity.
Qed.