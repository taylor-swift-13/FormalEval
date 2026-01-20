Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 5%Z 98765432101234567890123456787%Z 98765432101234567890123456792%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.