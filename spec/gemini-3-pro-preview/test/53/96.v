Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_528_830: add_spec 528 830 1358.
Proof.
  unfold add_spec.
  reflexivity.
Qed.