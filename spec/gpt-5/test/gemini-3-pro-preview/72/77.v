Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition sum_R (l : list R) : R := fold_right Rplus 0 l.

Definition will_it_fly_spec (q : list R) (w : R) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_R q <= w.

Example test_will_it_fly : will_it_fly_spec [48.77540799744989; -3.8838243003108204; -48.319352731351685] 2 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H. discriminate.
  - intros [Hpal _].
    simpl in Hpal.
    inversion Hpal.
    lra.
Qed.