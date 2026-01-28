Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_492_739: add_spec 492 739 1231.
Proof.
  unfold add_spec.
  reflexivity.
Qed.