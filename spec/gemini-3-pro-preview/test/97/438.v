Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6788_neg18 : multiply_spec 6788 (-18) 64.
Proof.
  unfold multiply_spec.
  (* 6788 mod 10 = 8, abs(-18) mod 10 = 8, 8 * 8 = 64 *)
  reflexivity.
Qed.