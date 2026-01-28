Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  (exists (ix iy iz : Z), IZR ix = x /\ IZR iy = y /\ IZR iz = z /\
    (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.7) (-123.79139763762555) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    inversion H.
  - intros [ix [iy [iz [Hx [Hy [Hz Hsum]]]]]].
    assert (Hbound: IZR (-124)%Z < -123.7 < IZR (-123)%Z).
    { lra. }
    rewrite <- Hx in Hbound.
    destruct Hbound as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.