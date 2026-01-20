Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 200; 300; 1/10; 2/10; 3/10; 2/10] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    specialize (H 100).
    assert (In 100 [100; 200; 300; 1/10; 2/10; 3/10; 2/10]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.