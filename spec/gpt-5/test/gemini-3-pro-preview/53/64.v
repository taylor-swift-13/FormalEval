Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_469_235 : add_spec 469 235 704.
Proof.
  unfold add_spec.
  reflexivity.
Qed.