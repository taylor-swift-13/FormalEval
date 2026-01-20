Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [10; 20; -30; 40; 500; 20] 126 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    specialize (H 500).
    assert (In 500 [10; 20; -30; 40; 500; 20]).
    { simpl. right. right. right. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.