Require Import Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition Spec(side high output : R) : Prop :=
  output = side * high / 2.

Example test_triangle_area :
  Spec 5 3 7.5.
Proof.
  unfold Spec.
  lra.
Qed.