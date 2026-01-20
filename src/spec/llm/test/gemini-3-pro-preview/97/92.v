Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg86_100 : multiply_spec (-86) 100 0.
Proof.
  unfold multiply_spec.
  (* |-86| mod 10 = 6, 100 mod 10 = 0, 6 * 0 = 0 *)
  reflexivity.
Qed.