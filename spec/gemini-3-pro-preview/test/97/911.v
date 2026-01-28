Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_5_neg123457 : multiply_spec 5 (-123457) 35.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.