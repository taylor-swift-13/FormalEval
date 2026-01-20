Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1234567889_246813580 : multiply_spec 1234567889 246813580 0.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.