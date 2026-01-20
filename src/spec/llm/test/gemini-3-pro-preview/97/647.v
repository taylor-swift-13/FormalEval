Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg10_neg8 : multiply_spec (-10) (-8) 0.
Proof.
  unfold multiply_spec.
  (* |-10| mod 10 = 0, |-8| mod 10 = 8, 0 * 8 = 0 *)
  reflexivity.
Qed.