Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000000000000000_999997 : add_spec 1000000000000000000 999997 1000000000000999997.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.