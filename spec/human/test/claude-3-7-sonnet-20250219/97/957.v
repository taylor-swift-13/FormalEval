Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387465_1234567895 :
  problem_97_spec 1092387465 1234567895 25.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.