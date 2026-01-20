Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1234567893_neg12347 : multiply_spec 1234567893 (-12347) 21.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.