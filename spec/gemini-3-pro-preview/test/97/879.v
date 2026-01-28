Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_32_31 : multiply_spec 32 31 2.
Proof.
  unfold multiply_spec.
  (* 32 mod 10 = 2, 31 mod 10 = 1, 2 * 1 = 2 *)
  reflexivity.
Qed.