Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1234567889_neg987654 : multiply_spec 1234567889 (-987654) 36.
Proof.
  unfold multiply_spec.
  (* 1234567889 mod 10 = 9, 987654 mod 10 = 4, 9 * 4 = 36 *)
  reflexivity.
Qed.