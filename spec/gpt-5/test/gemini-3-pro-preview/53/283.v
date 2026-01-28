Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9999_big : add_spec 9999 123456789098765432101234567889 123456789098765432101234577888.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.