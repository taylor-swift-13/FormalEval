Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 123456789098765432101234567890 98765432101234567890123456790 222222221199999999991358024680.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.