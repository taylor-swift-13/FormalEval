Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_123_neg12 : multiply_spec 123 (-12) 6.
Proof.
  unfold multiply_spec.
  (* 123 mod 10 = 3, |-12| mod 10 = 2, 3 * 2 = 6 *)
  reflexivity.
Qed.