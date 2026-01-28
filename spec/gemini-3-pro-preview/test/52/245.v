Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [8000001; 9999998; 10000000; 9000000; 10; 9999999; 8000000; 7000000; 6000000; 2000000; 9999998] 20 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (8000001 < 20).
    { apply H. simpl. left. reflexivity. }
    lia.
Qed.