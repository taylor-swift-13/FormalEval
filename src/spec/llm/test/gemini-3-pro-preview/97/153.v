Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg12345_neg12346 : multiply_spec (-12345) (-12346) 30.
Proof.
  unfold multiply_spec.
  (* Z.abs (-12345) mod 10 = 5, Z.abs (-12346) mod 10 = 6, 5 * 6 = 30 *)
  reflexivity.
Qed.