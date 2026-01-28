Require Import Reals.
Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition any_int_spec (x y z : R) (result : bool) : Prop :=
  result = true <-> (
    (exists n : Z, IZR n = x) /\
    (exists n : Z, IZR n = y) /\
    (exists n : Z, IZR n = z) /\
    (x = y + z \/ y = x + z \/ z = y + x)
  ).

Example test_any_int : any_int_spec 1.5 5 3.5 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate.
  - intros [[n Hn] _].
    assert (IZR 1 < 1.5 < IZR 2) by lra.
    rewrite <- Hn in H.
    destruct H as [H1 H2].
    apply lt_IZR in H1.
    apply lt_IZR in H2.
    lia.
Qed.