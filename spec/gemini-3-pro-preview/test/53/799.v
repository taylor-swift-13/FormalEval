Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_6_neg123456789098765432101234567891: add_spec 6 (-123456789098765432101234567891) (-123456789098765432101234567885).
Proof.
  unfold add_spec.
  reflexivity.
Qed.