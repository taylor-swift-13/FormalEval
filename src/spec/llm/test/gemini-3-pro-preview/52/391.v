Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [6.2] (-201) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    specialize (H 6.2).
    assert (In 6.2 [6.2]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.