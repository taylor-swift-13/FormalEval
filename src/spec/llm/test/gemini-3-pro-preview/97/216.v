Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475611_neg11 : multiply_spec 2938475611 (-11) 1.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.