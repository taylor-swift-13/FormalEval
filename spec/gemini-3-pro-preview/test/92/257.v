Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  (exists (ix iy iz : Z),
    x = IZR ix /\ y = IZR iy /\ z = IZR iz /\
    (ix = iy + iz \/ iy = ix + iz \/ iz = ix + iy)%Z).

Example test_any_int : any_int_spec 143.7 143.7 143.7 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [ix [iy [iz [Hx [Hy [Hz Hsum]]]]]].
    assert (H: IZR 143 < 143.7 < IZR 144) by lra.
    rewrite Hx in H.
    destruct H as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.