Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387464_neg975312471 :
  problem_97_spec 1092387464 (-975312471) 4.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.