Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1_neg16 : multiply_spec 1 (-16) 6.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.