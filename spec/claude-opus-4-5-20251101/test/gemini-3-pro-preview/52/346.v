Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [6.4133956835438735; 7.9] (-200) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 6.4133956835438735 [6.4133956835438735; 7.9]).
    { simpl. left. reflexivity. }
    specialize (H _ HIn).
    lra.
Qed.