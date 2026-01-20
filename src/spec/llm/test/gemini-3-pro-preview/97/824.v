Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6790_1234567889 : multiply_spec 6790 1234567889 0.
Proof.
  unfold multiply_spec.
  (* 6790 mod 10 = 0, 1234567889 mod 10 = 9, 0 * 9 = 0 *)
  reflexivity.
Qed.