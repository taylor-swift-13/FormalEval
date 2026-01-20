Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 98765432101234567890123456790 (-1000000000000000000000) 98765431101234567890123456790.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.