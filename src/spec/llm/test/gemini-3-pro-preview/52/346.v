Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [6.4133956835438735; 7.9] (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 6.4133956835438735).
    assert (In 6.4133956835438735 [6.4133956835438735; 7.9]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.