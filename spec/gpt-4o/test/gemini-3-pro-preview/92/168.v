Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <->
  (exists (ix iy iz : Z),
     IZR ix = x /\ IZR iy = y /\ IZR iz = z /\
     (ix = (iy + iz)%Z \/ iy = (ix + iz)%Z \/ iz = (ix + iy)%Z)).

Example test_any_int : any_int_spec (-123.04588347134523) (-123.04588347134523) (-123.04588347134523) false.
Proof.
  unfold any_int_spec.
  split.
  - intro H. discriminate.
  - intro H.
    destruct H as (ix & iy & iz & Hx & Hy & Hz & Hsum).
    assert (Hbound: -124 < -123.04588347134523 < -123) by lra.
    rewrite <- Hx in Hbound.
    destruct Hbound as [Hlow Hhigh].
    apply lt_IZR in Hlow.
    apply lt_IZR in Hhigh.
    lia.
Qed.