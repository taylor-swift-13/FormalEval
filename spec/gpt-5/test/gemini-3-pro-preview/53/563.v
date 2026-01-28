Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add : add_spec 7 (-999999999999999999997) (-999999999999999999990).
Proof.
  unfold add_spec.
  reflexivity.
Qed.