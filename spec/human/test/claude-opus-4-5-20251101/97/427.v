Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6787_2938475612 : problem_97_spec 6787 2938475612 14.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.