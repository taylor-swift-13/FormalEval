Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 66%Z 98765432101234567890123456790%Z 98765432101234567890123456856%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.