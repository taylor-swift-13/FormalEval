Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1234567892_1234567891 : multiply_spec 1234567892 1234567891 2.
Proof.
  unfold multiply_spec.
  (* 1234567892 mod 10 = 2, 1234567891 mod 10 = 1, 2 * 1 = 2 *)
  reflexivity.
Qed.