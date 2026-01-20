Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [-5; 10; -3; 1] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (In 10 [-5; 10; -3; 1]).
    { simpl. auto. }
    apply H in H0.
    lia.
Qed.