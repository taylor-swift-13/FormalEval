Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_negative_minus7_minus9 : problem_97_spec (-7) (-9) 63.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.