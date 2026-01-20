Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_3_1092387465 : multiply_spec 3 1092387465 15.
Proof.
  unfold multiply_spec.
  (* 3 mod 10 = 3, 1092387465 mod 10 = 5, 3 * 5 = 15 *)
  reflexivity.
Qed.