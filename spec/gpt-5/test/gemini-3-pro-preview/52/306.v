Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => x < t) l) /\
  (res = false <-> exists x, In x l /\ t <= x).

Example test_below_threshold : below_threshold_spec [5.5; 2.1549458848411773; 6.2; 7.9] (-30) false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      assert (In 5.5 [5.5; 2.1549458848411773; 6.2; 7.9]) by (left; reflexivity).
      rewrite Forall_forall in H.
      specialize (H _ H0).
      lra.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 5.5.
      split.
      * left; reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.