Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_550_501: add_spec 550 501 1051.
Proof.
  unfold add_spec.
  reflexivity.
Qed.