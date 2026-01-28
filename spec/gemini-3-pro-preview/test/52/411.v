Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [1000; 500; 250; 62.5; 30.807804019985152; 62.5] 200 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (In 1000 [1000; 500; 250; 62.5; 30.807804019985152; 62.5]).
    { simpl. left. reflexivity. }
    specialize (H 1000 H0).
    lra.
Qed.