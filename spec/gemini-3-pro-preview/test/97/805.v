Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg9_neg11 : multiply_spec (-9) (-11) 9.
Proof.
  unfold multiply_spec.
  (* Z.abs (-9) mod 10 = 9, Z.abs (-11) mod 10 = 1, 9 * 1 = 9 *)
  reflexivity.
Qed.