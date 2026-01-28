Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12346_neg9 : multiply_spec (-12346) (-9) 54.
Proof.
  unfold multiply_spec.
  (* 12346 mod 10 = 6, 9 mod 10 = 9, 6 * 9 = 54 *)
  reflexivity.
Qed.