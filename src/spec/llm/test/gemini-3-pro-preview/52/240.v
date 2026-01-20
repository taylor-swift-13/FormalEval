Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [-200; 300; 8000000; -400; -600; 300; 300] 125 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 300).
    assert (In 300 [-200; 300; 8000000; -400; -600; 300; 300]).
    { simpl. right. left. reflexivity. }
    apply H in H0.
    lia.
Qed.