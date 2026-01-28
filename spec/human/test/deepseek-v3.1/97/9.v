Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_neg6_neg9 : problem_97_spec (-6) (-9) 54.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.