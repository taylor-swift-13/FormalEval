Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg99_6785 : multiply_spec (-99) 6785 45.
Proof.
  unfold multiply_spec.
  (* |-99| mod 10 = 9, 6785 mod 10 = 5, 9 * 5 = 45 *)
  reflexivity.
Qed.