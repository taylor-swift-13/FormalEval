Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_473_231: add_spec 473 231 704.
Proof.
  unfold add_spec.
  reflexivity.
Qed.