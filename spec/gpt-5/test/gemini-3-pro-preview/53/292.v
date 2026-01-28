Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999997_999999 : add_spec 999997 999999 1999996.
Proof.
  unfold add_spec.
  reflexivity.
Qed.