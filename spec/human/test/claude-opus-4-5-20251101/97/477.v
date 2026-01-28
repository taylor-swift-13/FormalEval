Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_pre (a b : Z) : Prop := True.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg9876543211_1234567890 : problem_97_spec (-9876543211) 1234567890 0.
Proof.
  unfold problem_97_spec.
  simpl.
  reflexivity.
Qed.