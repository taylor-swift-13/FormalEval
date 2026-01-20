Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_76_67 : multiply_spec 76 67 42.
Proof.
  unfold multiply_spec.
  (* 76 mod 10 = 6, 67 mod 10 = 7, 6 * 7 = 42 *)
  reflexivity.
Qed.