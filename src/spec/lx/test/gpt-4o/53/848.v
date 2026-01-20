Require Import Coq.ZArith.ZArith.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = Z.add x y.

Example add_test :
  add_spec (-98765432101234567890123456790%Z) (-98765432101234567890123456790%Z) (-197530864202469135780246913580%Z).
Proof.
  unfold add_spec.
  reflexivity.
Qed.