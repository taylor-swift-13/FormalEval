Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [5.5%R; 6.2%R; 7.9%R; 8.1%R; 6.2%R; 6.2%R] 1%R false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 5.5%R).
    assert (In 5.5%R [5.5%R; 6.2%R; 7.9%R; 8.1%R; 6.2%R; 6.2%R]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.