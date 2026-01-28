Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_3_1000000000000000000002 : add_spec 3 1000000000000000000002 1000000000000000000005.
Proof.
  unfold add_spec.
  reflexivity.
Qed.