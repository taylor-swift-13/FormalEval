Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (x = y + z \/ y = x + z \/ z = x + y).

Example test_any_int : any_int_spec (-122.52113657785281) (-123.7) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate.
  - intros [H | [H | H]]; lra.
Qed.