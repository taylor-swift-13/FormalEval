Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Definition is_integer (x : R) : Prop := exists k : Z, IZR k = x.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> (is_integer x /\ is_integer y /\ is_integer z /\ (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec (-123.04588347134523) (-123.04588347134523) (-123.04588347134523) false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [H_int _].
    unfold is_integer in H_int.
    destruct H_int as [k Hk].
    assert (H1: IZR (-124) < -123.04588347134523) by lra.
    assert (H2: -123.04588347134523 < IZR (-123)) by lra.
    rewrite <- Hk in *.
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.