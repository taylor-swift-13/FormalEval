Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [-5; -4; -3] (-6) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    assert (C: -5 < -6).
    { apply H. simpl. left. reflexivity. }
    lia.
Qed.