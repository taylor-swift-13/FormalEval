Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [55/10; 79/10] (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      discriminate H.
    + intros H.
      assert (In (55/10) [55/10; 79/10]).
      { simpl. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ H0).
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists (55/10).
      split.
      * simpl. left. reflexivity.
      * lra.
    + intros _.
      reflexivity.
Qed.