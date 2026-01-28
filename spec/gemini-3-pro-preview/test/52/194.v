Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [1000; 500; 250; 125; 6.635714530100879; 62.5; 31.25] 2000000 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst; lra.
  - intros _.
    reflexivity.
Qed.