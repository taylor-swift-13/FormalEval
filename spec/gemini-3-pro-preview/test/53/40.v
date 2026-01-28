Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_571_697: add_spec 571 697 1268.
Proof.
  unfold add_spec.
  reflexivity.
Qed.