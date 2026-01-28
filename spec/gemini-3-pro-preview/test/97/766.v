Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg8_neg123457 : multiply_spec (-8) (-123457) 56.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.