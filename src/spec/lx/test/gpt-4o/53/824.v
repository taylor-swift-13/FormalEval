Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec 9998%Z 999999999999999999998%Z 1000000000000000009996%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.