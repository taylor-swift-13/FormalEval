Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_neg11_1092387466 : problem_97_spec (-11) 1092387466 6.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.