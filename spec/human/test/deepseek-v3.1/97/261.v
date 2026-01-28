Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_negative_inputs_equal : problem_97_spec (-123458) (-123458) 64.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.