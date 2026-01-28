Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg14_neg14 :
  problem_97_spec (-14) (-14) 16.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.