Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_5_123 : multiply_spec 5 123 15.
Proof.
  unfold multiply_spec.
  (* 5 mod 10 = 5, 123 mod 10 = 3, 5 * 3 = 15 *)
  reflexivity.
Qed.