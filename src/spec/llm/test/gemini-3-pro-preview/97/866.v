Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_246813579_5 : multiply_spec 246813579 5 45.
Proof.
  unfold multiply_spec.
  (* 246813579 mod 10 = 9, 5 mod 10 = 5, 9 * 5 = 45 *)
  reflexivity.
Qed.