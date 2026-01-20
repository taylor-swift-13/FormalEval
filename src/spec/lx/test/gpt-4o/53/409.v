Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 999999999999999999996%Z 999999999999999999997%Z 1999999999999999999993%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.