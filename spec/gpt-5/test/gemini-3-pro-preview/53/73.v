Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_191_93 : add_spec 191 93 284.
Proof.
  unfold add_spec.
  reflexivity.
Qed.