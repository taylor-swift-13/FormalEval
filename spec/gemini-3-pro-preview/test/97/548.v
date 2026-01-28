Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6786_neg975312468 : multiply_spec 6786 (-975312468) 48.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.