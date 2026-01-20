Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg123456_neg12346 : multiply_spec (-123456) (-12346) 36.
Proof.
  unfold multiply_spec.
  (* |-123456| mod 10 = 6, |-12346| mod 10 = 6, 6 * 6 = 36 *)
  reflexivity.
Qed.