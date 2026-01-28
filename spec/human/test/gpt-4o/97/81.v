Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example problem_97_test_1 : problem_97_spec 123 (-8) 24.
Proof.
  unfold problem_97_spec.
  assert (Z.abs 123 mod 10 = 3) as H1.
  { reflexivity. }
  assert (Z.abs (-8) mod 10 = 8) as H2.
  { reflexivity. }
  rewrite H1, H2.
  simpl.
  reflexivity.
Qed.