Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 123456789098765432101234567891%Z 4%Z 123456789098765432101234567895%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.