Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_452_186: add_spec 452 186 638.
Proof.
  unfold add_spec.
  reflexivity.
Qed.