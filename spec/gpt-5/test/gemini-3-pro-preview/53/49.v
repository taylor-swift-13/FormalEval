Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_818_902 : add_spec 818 902 1720.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.