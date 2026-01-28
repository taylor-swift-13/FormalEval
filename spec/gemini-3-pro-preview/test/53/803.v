Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1: add_spec 999999999999999999998%Z (-123456789098765432101234567891%Z) (-123456788098765432101234567893%Z).
Proof.
  unfold add_spec.
  reflexivity.
Qed.