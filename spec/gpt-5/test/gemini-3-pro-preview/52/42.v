Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [3.5; 2.6445924145352944; 2.2; 1.1] 3 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      specialize (H 3.5 (or_introl eq_refl)).
      lra.
  - split.
    + intros _.
      exists 3.5.
      split.
      * left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.