Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec (-9999%Z) (1000000000000000000001%Z) (999999999999999990002%Z).
Proof.
  unfold add_spec.
  reflexivity.
Qed.