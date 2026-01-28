Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H.
      discriminate H.
    + intros H.
      assert (In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2]).
      { left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H 100 H0).
      lra.
  - split.
    + intros _.
      exists 100.
      split.
      * left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.