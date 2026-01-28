Require Import ZArith.
Require Import Znumtheory.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example problem_97_test_1 : problem_97_spec (-9) (-10) 0.
Proof.
  unfold problem_97_spec.
  assert (Z.abs (-9) mod 10 = 9) as H1.
  { reflexivity. }
  assert (Z.abs (-10) mod 10 = 0) as H2.
  { reflexivity. }
  rewrite H1, H2.
  simpl.
  reflexivity.
Qed.