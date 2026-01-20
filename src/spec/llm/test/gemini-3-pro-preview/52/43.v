Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [0; -1; -2; -4] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    assert (0 < 0).
    { apply H. simpl. left. reflexivity. }
    lia.
Qed.