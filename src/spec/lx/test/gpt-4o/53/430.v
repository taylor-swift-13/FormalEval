Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 1000%Z 98765432101234567890123456788%Z 98765432101234567890123457788%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.