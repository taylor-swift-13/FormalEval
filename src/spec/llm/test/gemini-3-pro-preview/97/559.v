Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12347_2 : multiply_spec (-12347) 2 14.
Proof.
  unfold multiply_spec.
  (* 12347 mod 10 = 7, 2 mod 10 = 2, 7 * 2 = 14 *)
  reflexivity.
Qed.