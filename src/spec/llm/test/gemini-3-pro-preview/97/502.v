Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12_6789 : multiply_spec (-12) 6789 18.
Proof.
  unfold multiply_spec.
  (* |-12| mod 10 = 2, 6789 mod 10 = 9, 2 * 9 = 18 *)
  reflexivity.
Qed.