Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg10_neg12344 : multiply_spec (-10) (-12344) 0.
Proof.
  unfold multiply_spec.
  (* |-10| mod 10 = 0, |-12344| mod 10 = 4, 0 * 4 = 0 *)
  reflexivity.
Qed.