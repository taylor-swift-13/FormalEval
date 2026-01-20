Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6788_2938475611 : multiply_spec 6788 2938475611 8.
Proof.
  unfold multiply_spec.
  (* 6788 mod 10 = 8, 2938475611 mod 10 = 1, 8 * 1 = 8 *)
  reflexivity.
Qed.