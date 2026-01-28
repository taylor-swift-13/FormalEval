Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition is_int (r : R) : Prop := exists z : Z, IZR z = r.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_int x /\ is_int y /\ is_int z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-121.05003417314278) (-123.7) (-122.24385010385771) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [_ [H_int _]].
    destruct H_int as [z Hz].
    assert (H_bounds : -124 < -123.7 < -123) by lra.
    rewrite <- Hz in H_bounds.
    destruct H_bounds as [H_lower H_upper].
    apply lt_IZR in H_lower.
    apply lt_IZR in H_upper.
    lia.
Qed.