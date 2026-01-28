Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 98765432101234567890123456788%Z 999999999999999999998%Z 98765433101234567890123456786%Z.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.