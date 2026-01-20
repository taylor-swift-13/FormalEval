Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_0_5 : multiply_spec 0 5 0.
Proof.
  unfold multiply_spec.
  (* 0 mod 10 = 0, 5 mod 10 = 5, 0 * 5 = 0 *)
  reflexivity.
Qed.