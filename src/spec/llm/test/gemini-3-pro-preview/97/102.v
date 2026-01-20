Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg17_neg87 : multiply_spec (-17) (-87) 49.
Proof.
  unfold multiply_spec.
  (* Z.abs (-17) mod 10 = 7, Z.abs (-87) mod 10 = 7, 7 * 7 = 49 *)
  reflexivity.
Qed.