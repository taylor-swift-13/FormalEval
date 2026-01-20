Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition sum_list (l : list R) : R :=
  fold_right Rplus 0 l.

Definition will_it_fly_spec (q : list R) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= IZR w).

Example test_will_it_fly : will_it_fly_spec [48.77540799744989%R; -48.319352731351685%R; -3.8838243003108204%R; -48.319352731351685%R] 2%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    discriminate.
  - intros [Hrev _].
    simpl in Hrev.
    injection Hrev as H1.
    lra.
Qed.