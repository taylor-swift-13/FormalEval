Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg6_neg9 : multiply_spec (-6) (-9) 54.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.