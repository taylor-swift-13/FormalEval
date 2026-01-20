Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [100; 250; 2000000; 300; -400; 500; -600] 1998 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 2000000).
    assert (H_in : In 2000000 [100; 250; 2000000; 300; -400; 500; -600]).
    { simpl. right. right. left. reflexivity. }
    apply H in H_in.
    lia.
Qed.