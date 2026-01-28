Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387464_246813583 :
  problem_97_spec 1092387464 246813583 12.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.