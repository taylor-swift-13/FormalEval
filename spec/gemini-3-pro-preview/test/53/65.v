Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_91_322: add_spec 91 322 413.
Proof.
  unfold add_spec.
  reflexivity.
Qed.