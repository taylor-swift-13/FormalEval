Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec (-1000002) (-999999) (-2000001).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.