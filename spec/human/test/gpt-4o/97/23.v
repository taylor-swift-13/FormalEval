Require Import ZArith.
Require Import Znumtheory. (* For Zmod_divide *)
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example problem_97_test_1 : problem_97_spec 123 (-12) 6.
Proof.
  unfold problem_97_spec.
  assert (Z.abs 123 mod 10 = 3) as H1.
  { reflexivity. }
  assert (Z.abs (-12) mod 10 = 2) as H2.
  { reflexivity. }
  rewrite H1, H2.
  simpl.
  reflexivity.
Qed.