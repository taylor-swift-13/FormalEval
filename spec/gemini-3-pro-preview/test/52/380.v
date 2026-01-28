Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [5.5; 6.2212876393256; 6.2; 7.9; 6.2] (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 5.5).
    assert (In 5.5 [5.5; 6.2212876393256; 6.2; 7.9; 6.2]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.