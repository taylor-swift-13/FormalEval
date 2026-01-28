Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_361_945: add_spec 361 945 1306.
Proof.
  unfold add_spec.
  reflexivity.
Qed.