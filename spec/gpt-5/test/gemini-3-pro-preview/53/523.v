Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 9998 98765432101234567890123456786 98765432101234567890123466784.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.