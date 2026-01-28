Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_567_768: add_spec 567 768 1335.
Proof.
  unfold add_spec.
  reflexivity.
Qed.