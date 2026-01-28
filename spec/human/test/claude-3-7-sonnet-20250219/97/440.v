Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg123458_6786 :
  problem_97_spec (-123458) 6786 48.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.