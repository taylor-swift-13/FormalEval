Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec (-10000) 999999999999999999999 999999999999999989999.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.