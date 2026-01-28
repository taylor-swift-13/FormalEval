Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 999999999999999999997 98765432101234567890123456788 98765433101234567890123456785.
Proof.
  unfold add_spec.
  reflexivity.
Qed.