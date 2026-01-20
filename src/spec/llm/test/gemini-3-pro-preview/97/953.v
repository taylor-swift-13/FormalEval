Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_246813582_neg99 : multiply_spec 246813582 (-99) 18.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.