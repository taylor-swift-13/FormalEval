Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg14_neg14 : multiply_spec (-14) (-14) 16.
Proof.
  unfold multiply_spec.
  (* abs(-14) mod 10 = 4, abs(-14) mod 10 = 4, 4 * 4 = 16 *)
  reflexivity.
Qed.