Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_124_100 : multiply_spec 124 100 0.
Proof.
  unfold multiply_spec.
  (* 124 mod 10 = 4, 100 mod 10 = 0, 4 * 0 = 0 *)
  reflexivity.
Qed.