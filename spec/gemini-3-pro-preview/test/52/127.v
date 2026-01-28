Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [62.5; 16.953176162073675; 2.9851560365316985] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (In 62.5 [62.5; 16.953176162073675; 2.9851560365316985]).
    { simpl. left. reflexivity. }
    specialize (H 62.5 H0).
    lra.
Qed.