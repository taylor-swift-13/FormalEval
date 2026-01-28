Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_826_822: add_spec 826 822 1648.
Proof.
  unfold add_spec.
  reflexivity.
Qed.