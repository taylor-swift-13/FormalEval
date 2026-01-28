Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475612_6785 : multiply_spec 2938475612 6785 10.
Proof.
  unfold multiply_spec.
  (* 2938475612 mod 10 = 2, 6785 mod 10 = 5, 2 * 5 = 10 *)
  reflexivity.
Qed.