Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_966_528: add_spec 966 528 1494.
Proof.
  unfold add_spec.
  reflexivity.
Qed.