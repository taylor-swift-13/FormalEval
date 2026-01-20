Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6788_1234567892 : multiply_spec 6788 1234567892 16.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.