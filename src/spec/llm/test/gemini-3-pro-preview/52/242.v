Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000] 9999998 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (Hin: In 10000000 [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000]).
    { simpl. right. right. right. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.