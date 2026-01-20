Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_example : add_spec 0 1 1.
Proof.
  unfold add_spec.
  lia.
Qed.