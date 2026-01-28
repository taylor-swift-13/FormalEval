Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 1092387467%Z 1092387466%Z 42%Z.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.