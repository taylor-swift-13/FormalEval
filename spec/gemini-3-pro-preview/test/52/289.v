Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold_2: below_threshold_spec [100; 2000000; 300; -400; 500] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    assert (H_in : In 100 [100; 2000000; 300; -400; 500]).
    { simpl. left. reflexivity. }
    apply H in H_in.
    lia.
Qed.