Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_818_902: add_spec 818 902 1720.
Proof.
  unfold add_spec.
  reflexivity.
Qed.