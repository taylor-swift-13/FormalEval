Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_59_772: add_spec 59 772 831.
Proof.
  unfold add_spec.
  reflexivity.
Qed.