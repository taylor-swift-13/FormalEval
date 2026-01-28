Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 999999999999999999998 (-123456789098765432101234567891) (-123456788098765432101234567893).
Proof.
  unfold add_spec.
  reflexivity.
Qed.