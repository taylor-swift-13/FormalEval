Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_666_55: add_spec 666 55 721.
Proof.
  unfold add_spec.
  reflexivity.
Qed.