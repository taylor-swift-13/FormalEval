Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec (-123456789098765432101234567889) 999999999999999999999 (-123456788098765432101234567890).
Proof.
  unfold add_spec.
  reflexivity.
Qed.