Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_99_98 : add_spec 99 98 197.
Proof.
  unfold add_spec.
  reflexivity.
Qed.