Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475609_9876543210 :
  problem_97_spec 2938475609 9876543210 0.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.