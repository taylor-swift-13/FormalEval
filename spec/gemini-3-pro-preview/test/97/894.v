Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6792_246813581 : multiply_spec 6792 246813581 2.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.