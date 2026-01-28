Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_97_96: add_spec 97 96 193.
Proof.
  unfold add_spec.
  reflexivity.
Qed.