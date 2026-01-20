Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg123459_neg123459 : multiply_spec (-123459) (-123459) 81.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.