Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6786_1092387466 : multiply_spec 6786 1092387466 36.
Proof.
  unfold multiply_spec.
  (* 6786 mod 10 = 6, 1092387466 mod 10 = 6, 6 * 6 = 36 *)
  reflexivity.
Qed.