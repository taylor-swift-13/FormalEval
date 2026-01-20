Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg18_3 : multiply_spec (-18) 3 24.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.