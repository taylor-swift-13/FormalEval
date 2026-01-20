Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec (-8%Z) (-3%Z) (-11%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.