Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg9876543212_neg9876543211 : problem_97_spec (-9876543212) (-9876543211) 2.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.