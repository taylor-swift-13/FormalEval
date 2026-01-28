Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 999999999999999999%Z 98765432101234567890123456789%Z 98765432102234567890123456788%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.