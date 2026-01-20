Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 1000000000000000000002%Z 1000000000000000000000%Z 2000000000000000000002%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.