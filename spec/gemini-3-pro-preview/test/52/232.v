Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [-200; 10; 20; -30; 40; 8000000; -50] 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (In 8000000 [-200; 10; 20; -30; 40; 8000000; -50]) as Hin.
    { simpl. do 5 right. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.