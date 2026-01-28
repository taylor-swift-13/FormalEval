Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_228_863: add_spec 228 863 1091.
Proof.
  unfold add_spec.
  reflexivity.
Qed.