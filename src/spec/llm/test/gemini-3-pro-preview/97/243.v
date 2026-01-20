Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg987657_1234567890 : multiply_spec (-987657) 1234567890 0.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.