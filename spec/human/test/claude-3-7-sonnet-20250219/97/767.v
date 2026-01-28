Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387466_246813580 :
  problem_97_spec 1092387466 246813580 0.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.