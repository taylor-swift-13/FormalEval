Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg99_large : add_spec (-99) 1000000000000000001 999999999999999902.
Proof.
  unfold add_spec.
  reflexivity.
Qed.