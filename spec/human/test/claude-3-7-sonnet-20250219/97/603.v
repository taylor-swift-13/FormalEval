Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_246813579_neg975312469 :
  problem_97_spec 246813579 (-975312469) 81.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.