Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [100; 200; 300; 0.2; 0.3] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (In 100 [100; 200; 300; 0.2; 0.3]).
    { simpl. left. reflexivity. }
    specialize (H 100 H0).
    lra.
Qed.