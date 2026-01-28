Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_671_705: add_spec 671 705 1376.
Proof.
  unfold add_spec.
  reflexivity.
Qed.