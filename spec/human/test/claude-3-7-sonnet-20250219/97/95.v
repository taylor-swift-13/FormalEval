Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_9_neg12 :
  problem_97_spec 9 (-12) 18.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.