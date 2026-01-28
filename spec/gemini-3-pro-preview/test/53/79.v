Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_876_389: add_spec 876 389 1265.
Proof.
  unfold add_spec.
  reflexivity.
Qed.