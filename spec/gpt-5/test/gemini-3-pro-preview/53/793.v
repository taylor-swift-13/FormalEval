Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000_neg999997 : add_spec 1000000 (-999997) 3.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.