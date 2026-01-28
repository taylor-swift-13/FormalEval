Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387466_1092387465 :
  problem_97_spec 1092387466 1092387465 30.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.