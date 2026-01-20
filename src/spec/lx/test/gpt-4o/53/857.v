Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec (-9998%Z) (-9997%Z) (-19995%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.