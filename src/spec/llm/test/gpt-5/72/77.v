Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.

Open Scope R_scope.

Definition sum_R (l : list R) : R := fold_right Rplus 0%R l.

Definition will_it_fly_spec (q : list R) (w : R) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_R q <= w.

Example will_it_fly_test :
  will_it_fly_spec
    [48.77540799744989%R; -3.8838243003108204%R; -48.319352731351685%R]
    2%R
    false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H. discriminate H.
  - intros [Heq _].
    simpl in Heq.
    pose proof (f_equal (@hd R 0%R) Heq) as Hhd.
    simpl in Hhd.
    assert (-48.319352731351685%R < 48.77540799744989%R) by lra.
    rewrite Hhd in H.
    exfalso.
    apply (Rlt_irrefl (-48.319352731351685%R)).
    exact H.
Qed.