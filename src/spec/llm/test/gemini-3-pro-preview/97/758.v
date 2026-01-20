Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg975312470_246813582 : multiply_spec (-975312470) 246813582 0.
Proof.
  unfold multiply_spec.
  (* abs(-975312470) mod 10 = 0, 246813582 mod 10 = 2, 0 * 2 = 0 *)
  reflexivity.
Qed.