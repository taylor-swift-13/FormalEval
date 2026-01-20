Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12_1234567888 : multiply_spec (-12) 1234567888 16.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.