Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec (-2147483648%Z) (-1%Z) (-2147483649%Z).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.