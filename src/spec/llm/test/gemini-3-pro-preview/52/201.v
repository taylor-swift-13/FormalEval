Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [10000000; 8000002; 9000000; 8000001; 8000000; 7000000; 6000000; 2000000; 7000000] 125 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (Hin: In 10000000 [10000000; 8000002; 9000000; 8000001; 8000000; 7000000; 6000000; 2000000; 7000000]).
    { simpl. left. reflexivity. }
    apply H in Hin.
    lia.
Qed.