Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg_9876543211_246813579 : multiply_spec (-9876543211) 246813579 9.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.