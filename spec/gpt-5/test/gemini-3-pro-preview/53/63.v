Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_724_18 : add_spec 724 18 742.
Proof.
  unfold add_spec.
  reflexivity.
Qed.