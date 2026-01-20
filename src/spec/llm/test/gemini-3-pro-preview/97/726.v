Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg123457_2938475609 : multiply_spec (-123457) 2938475609 63.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.