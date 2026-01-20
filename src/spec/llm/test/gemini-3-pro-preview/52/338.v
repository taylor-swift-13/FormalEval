Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [5.5%R; 6.2%R; 7.9%R; 7.9%R] 300%R true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]]; subst; lra.
  - intros _.
    reflexivity.
Qed.