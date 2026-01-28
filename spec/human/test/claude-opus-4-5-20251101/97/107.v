Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg17_3 : problem_97_spec (-17) 3 21.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.