Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec (-2) (-1000000000000000000000) (-1000000000000000000002).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.