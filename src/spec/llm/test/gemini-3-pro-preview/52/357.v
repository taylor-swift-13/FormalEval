Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 200; 300; 0.1; 0.2; 0.3; 0.2] 40 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    specialize (H 100).
    assert (In 100 [100; 200; 300; 0.1; 0.2; 0.3; 0.2]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.