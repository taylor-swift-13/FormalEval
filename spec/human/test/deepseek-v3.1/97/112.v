Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg99_neg99 : problem_97_spec (-99) (-99) 81.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.