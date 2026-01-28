Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10002_large : add_spec 10002 123456789098765432101234567889 123456789098765432101234577891.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.