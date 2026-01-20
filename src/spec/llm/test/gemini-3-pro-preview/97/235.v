Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg_987656_neg_123457 : multiply_spec (-987656) (-123457) 42.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.