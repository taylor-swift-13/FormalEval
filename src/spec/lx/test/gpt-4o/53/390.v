Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec (-999998) (-999998) (-1999996).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.