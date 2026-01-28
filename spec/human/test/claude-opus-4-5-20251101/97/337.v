Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475611_2938475609 : problem_97_spec 2938475611 2938475609 9.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.