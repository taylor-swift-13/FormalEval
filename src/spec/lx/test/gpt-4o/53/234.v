Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 999999999999999999999 5 1000000000000000000004.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.