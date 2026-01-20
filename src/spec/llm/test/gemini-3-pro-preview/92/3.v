Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  ((exists ix, IZR ix = x) /\ (exists iy, IZR iy = y) /\ (exists iz, IZR iz = z) /\
   (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec 1.5 5 3.5 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H.
    discriminate.
  - intros [Hx _].
    destruct Hx as [ix Hix].
    assert (1 < IZR ix < 2).
    { rewrite Hix. split; lra. }
    destruct H as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.