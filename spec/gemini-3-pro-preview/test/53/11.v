Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_197_326: add_spec 197 326 523.
Proof.
  unfold add_spec.
  reflexivity.
Qed.