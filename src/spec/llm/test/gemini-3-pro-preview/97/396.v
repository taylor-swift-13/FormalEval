Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_987655_987654 : multiply_spec 987655 987654 20.
Proof.
  unfold multiply_spec.
  (* 987655 mod 10 = 5, 987654 mod 10 = 4, 5 * 4 = 20 *)
  reflexivity.
Qed.