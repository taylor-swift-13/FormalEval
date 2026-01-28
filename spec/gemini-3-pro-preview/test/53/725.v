Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1: add_spec 1000000000000000000 (-999997) 999999999999000003.
Proof.
  unfold add_spec.
  reflexivity.
Qed.