Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.7) (-123.04588347134523) (-123.7) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [Hx _].
    unfold is_int in Hx. destruct Hx as [n Hn].
    assert (H : -124 < -123.7 < -123) by lra.
    rewrite <- Hn in H.
    destruct H as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.