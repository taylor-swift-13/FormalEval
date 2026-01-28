Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [3.5; 2.6445924145352944; 2.2; 1.1] 3 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 3.5 [3.5; 2.6445924145352944; 2.2; 1.1]).
    { simpl. left. reflexivity. }
    specialize (H 3.5 HIn).
    lra.
Qed.