Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000002_1000001 : add_spec 1000002 1000001 2000003.
Proof.
  unfold add_spec.
  reflexivity.
Qed.