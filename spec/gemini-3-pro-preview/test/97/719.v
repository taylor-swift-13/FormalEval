Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg16_3 : multiply_spec (-16) 3 18.
Proof.
  unfold multiply_spec.
  (* |-16| mod 10 = 6, 3 mod 10 = 3, 6 * 3 = 18 *)
  reflexivity.
Qed.