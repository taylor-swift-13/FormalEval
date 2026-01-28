Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_0_123456789098765432101234567891 : add_spec 0 123456789098765432101234567891 123456789098765432101234567891.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.