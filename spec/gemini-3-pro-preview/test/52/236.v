Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 2000000; 10000002; 500; 8000002] 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    specialize (H 10000002).
    assert (H_in : In 10000002 [100; 2000000; 10000002; 500; 8000002]).
    { simpl. right. right. left. reflexivity. }
    apply H in H_in.
    lia.
Qed.