Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (x = y + z \/ y = x + z \/ z = x + y).

Example test_any_int : any_int_spec (-26.09071999120809) 65.58608597419911 (-43.14648859197439) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    lra.
Qed.