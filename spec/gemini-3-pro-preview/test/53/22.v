Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_890_180: add_spec 890 180 1070.
Proof.
  unfold add_spec.
  reflexivity.
Qed.