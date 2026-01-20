Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [1000; 500; 250; 125; 6; 62; 31; 31] 499 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (Hin : In 1000 [1000; 500; 250; 125; 6; 62; 31; 31]).
    { simpl. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.