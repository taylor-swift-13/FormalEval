Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 62.5; 30.807804019985152] (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 1000).
    assert (In 1000 [1000; 500; 250; 62.5; 30.807804019985152]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.