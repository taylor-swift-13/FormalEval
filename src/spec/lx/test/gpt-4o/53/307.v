Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 999999999999999999999%Z 98765432101234567890123456788%Z 98765433101234567890123456787%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.