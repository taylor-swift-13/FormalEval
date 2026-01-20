Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example add_test :
  add_spec 98765432101234567890123456788 98765432101234567890123456789 197530864202469135780246913577.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.