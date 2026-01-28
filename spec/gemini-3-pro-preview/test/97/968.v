Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12_1092387466 : multiply_spec (-12) 1092387466 12.
Proof.
  unfold multiply_spec.
  (* abs(-12) mod 10 = 2, abs(1092387466) mod 10 = 6, 2 * 6 = 12 *)
  reflexivity.
Qed.