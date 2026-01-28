Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1_98765432101234567890123456790 : add_spec 1 98765432101234567890123456790 98765432101234567890123456791.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.