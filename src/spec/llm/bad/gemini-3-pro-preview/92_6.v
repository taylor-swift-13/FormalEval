Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Open Scope R_scope.

Definition any_int_spec (x y z : R) (res : bool) : Prop :=
  res = true <-> 
  ((exists n : Z, x = IZR n) /\ 
   (exists n : Z, y = IZR n) /\ 
   (exists n : Z, z = IZR n) /\ 
   (x = y + z \/ y = x + z \/ z = x + y)).

Example test_any_int : any_int_spec 2.2 2.2 2.2 false.
Proof.
  unfold any_int_spec.
  split.
  - intros H. discriminate H.
  - intros [Hx _].
    destruct Hx as [n Hn].
    assert (H : 2 < 2.2 < 3) by lra.
    rewrite Hn in H.
    destruct H as [H1 H2].
    replace 2 with (IZR 2) in H1 by reflexivity.
    replace 3 with (IZR 3) in H2 by reflexivity.
    apply IZR_lt in H1.
    apply IZR_lt in H2.
    lia.
Qed.