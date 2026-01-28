Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999996_999997: add_spec 999996 999997 1999993.
Proof.
  unfold add_spec.
  reflexivity.
Qed.