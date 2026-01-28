Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_minus17_minus17 : problem_97_spec (-17) (-17) 49.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.