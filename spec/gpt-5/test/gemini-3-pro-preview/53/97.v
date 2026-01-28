Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_492_739 : add_spec 492 739 1231.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.