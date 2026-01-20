Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [5.5; 6.2; 7.9; 8.1; 8.855464118192813; 5.6573184258702085; 11.869088428731756; 6.2] 10000001 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst; lra.
  - intros _.
    reflexivity.
Qed.