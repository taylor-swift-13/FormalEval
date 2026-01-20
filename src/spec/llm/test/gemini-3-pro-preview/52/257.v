Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [10; 6000001; -30; 40; -50] 13 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 6000001).
    assert (In 6000001 [10; 6000001; -30; 40; -50]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.