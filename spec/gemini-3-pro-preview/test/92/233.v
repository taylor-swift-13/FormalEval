Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> ((exists i : Z, IZR i = x) /\ (exists j : Z, IZR j = y) /\ (exists k : Z, IZR k = z) /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-17) (-123.04588347134523) (-122.24385010385771) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. inversion H.
  - intros [Hx [Hy [Hz Hsum]]].
    destruct Hy as [iy Heq].
    assert (H_bound: -124 < -123.04588347134523 < -123).
    { lra. }
    rewrite <- Heq in H_bound.
    destruct H_bound as [H_lo H_hi].
    replace (-124) with (IZR (-124)) in H_lo by reflexivity.
    replace (-123) with (IZR (-123)) in H_hi by reflexivity.
    apply lt_IZR in H_lo.
    apply lt_IZR in H_hi.
    lia.
Qed.