Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_882_225: add_spec 882 225 1107.
Proof.
  unfold add_spec.
  reflexivity.
Qed.