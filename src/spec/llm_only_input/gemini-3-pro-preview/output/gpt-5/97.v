Require Import ZArith.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_example : multiply_spec 148%Z 412%Z 16%Z.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.