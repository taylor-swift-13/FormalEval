Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_300_77: add_spec 300 77 377.
Proof.
  unfold add_spec.
  reflexivity.
Qed.