Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9999_1000000000000000000001 : add_spec 9999 1000000000000000000001 1000000000000000010000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.