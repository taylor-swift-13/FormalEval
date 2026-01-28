Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 1000000000000000000003 999999 1000000000000001000002.
Proof.
  unfold add_spec.
  reflexivity.
Qed.