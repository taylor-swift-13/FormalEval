Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [62.5; 16.953176162073675; 2.9851560365316985; 16.953176162073675] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (HIn : In 62.5 [62.5; 16.953176162073675; 2.9851560365316985; 16.953176162073675]).
    { simpl. left. reflexivity. }
    specialize (H 62.5 HIn).
    lra.
Qed.