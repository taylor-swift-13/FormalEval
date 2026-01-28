Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1234567892_neg9 : problem_97_spec 1234567892 (-9) 18.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.