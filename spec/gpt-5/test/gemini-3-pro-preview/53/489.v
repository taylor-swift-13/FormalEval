Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000001_123456789098765432101234567893 : add_spec 1000001 123456789098765432101234567893 123456789098765432101235567894.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.