Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 125; 62.5; 31.25] 125 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 1000 [1000; 500; 250; 125; 62.5; 31.25]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lra.
Qed.