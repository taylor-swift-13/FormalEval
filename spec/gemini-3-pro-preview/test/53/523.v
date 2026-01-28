Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_98765432101234567890123456786: add_spec 9998 98765432101234567890123456786 98765432101234567890123466784.
Proof.
  unfold add_spec.
  reflexivity.
Qed.