Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg86_neg86 : multiply_spec (-86) (-86) 36.
Proof.
  unfold multiply_spec.
  (* Z.abs (-86) mod 10 = 6, Z.abs (-86) mod 10 = 6, 6 * 6 = 36 *)
  reflexivity.
Qed.