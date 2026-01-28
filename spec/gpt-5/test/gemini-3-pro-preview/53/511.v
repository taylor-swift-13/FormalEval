Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_big : add_spec 98765432101234567890123456788 999998 98765432101234567890124456786.
Proof.
  unfold add_spec.
  reflexivity.
Qed.