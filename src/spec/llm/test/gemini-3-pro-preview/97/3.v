Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2020_1851 : multiply_spec 2020 1851 0.
Proof.
  unfold multiply_spec.
  (* 2020 mod 10 = 0, 1851 mod 10 = 1, 0 * 1 = 0 *)
  reflexivity.
Qed.