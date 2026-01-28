Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [6.576799211228067%R; 5.5%R; 1.5311576847949309%R; 5.50048632089892%R; 6.2212876393256%R; 7.9%R; 7.9%R] (-199)%R false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 5.5%R).
    assert (In 5.5%R [6.576799211228067%R; 5.5%R; 1.5311576847949309%R; 5.50048632089892%R; 6.2212876393256%R; 7.9%R; 7.9%R]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lra.
Qed.