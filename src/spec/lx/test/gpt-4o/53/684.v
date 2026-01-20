Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 1000000000000000000000 1000000000000000000 1001000000000000000000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.