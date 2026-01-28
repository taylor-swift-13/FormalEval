Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  (exists (ix iy iz : Z), IZR ix = x /\ IZR iy = y /\ IZR iz = z /\
    (ix = iy + iz \/ iy = ix + iz \/ iz = ix + iy))%Z.

Example test_any_int : any_int_spec (-5) (-123.80980628085806) (-122.24385010385771) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [ix [iy [iz [Hx [Hy [Hz _]]]]]].
    assert (Hbounds: IZR (-124) < -123.80980628085806 < IZR (-123)).
    { lra. }
    rewrite <- Hy in Hbounds.
    destruct Hbounds as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.