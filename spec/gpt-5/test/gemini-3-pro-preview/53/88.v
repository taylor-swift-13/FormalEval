Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_843_872 : add_spec 843 872 1715.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.