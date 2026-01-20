Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [1; 4; 7; 10; 7] 5 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    assert (In 7 [1; 4; 7; 10; 7]) as HIn.
    { simpl. auto. }
    specialize (H 7 HIn).
    lia.
Qed.