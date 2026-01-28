Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_large_negatives : problem_97_spec 1234567889 (-987654) 36.
Proof.
  unfold problem_97_spec.
  simpl.
  rewrite Z.abs_eq.
  rewrite Z.abs_eq.
  reflexivity.
Qed.