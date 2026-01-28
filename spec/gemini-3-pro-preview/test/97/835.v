Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6790_6791 : multiply_spec 6790 6791 0.
Proof.
  unfold multiply_spec.
  (* 6790 mod 10 = 0, 6791 mod 10 = 1, 0 * 1 = 0 *)
  reflexivity.
Qed.