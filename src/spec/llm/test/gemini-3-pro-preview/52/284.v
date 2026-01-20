Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [2000000; 10000001; 9000000; 8000000; 6000000; 2000000; 8000000] 10000001 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (10000001 < 10000001).
    { apply H. simpl. right. left. reflexivity. }
    lia.
Qed.