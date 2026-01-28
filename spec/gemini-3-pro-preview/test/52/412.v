Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [-400; 100; -200; 300; -400; 500; -600; -600] 302 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 500).
    assert (In 500 [-400; 100; -200; 300; -400; 500; -600; -600]) as Hin.
    { simpl. do 5 right. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.