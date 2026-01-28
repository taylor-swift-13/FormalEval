Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_843_872: add_spec 843 872 1715.
Proof.
  unfold add_spec.
  reflexivity.
Qed.