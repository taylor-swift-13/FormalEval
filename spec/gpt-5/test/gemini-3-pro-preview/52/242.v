Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000] 9999998 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      specialize (H 10000000).
      assert (In 10000000 [2000000; 8000001; 1000; 10000000; 8000001; 10; 8000000; 2000000; 6000000; 2000000; 2000000]) as HIn.
      { simpl. do 3 right. left. reflexivity. }
      apply H in HIn.
      lia.
  - split.
    + intros _.
      exists 10000000.
      split.
      * simpl. do 3 right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.