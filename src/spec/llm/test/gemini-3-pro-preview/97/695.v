Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6789_neg98 : multiply_spec 6789 (-98) 72.
Proof.
  unfold multiply_spec.
  (* 6789 mod 10 = 9, abs(-98) mod 10 = 8, 9 * 8 = 72 *)
  reflexivity.
Qed.