Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large_neg : add_spec (-9998) (-999999999999999999999) (-1000000000000000009997).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.