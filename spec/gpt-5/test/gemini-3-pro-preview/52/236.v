Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; 2000000; 10000002; 500; 8000002] 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      specialize (H 10000002).
      assert (HIn : In 10000002 [100; 2000000; 10000002; 500; 8000002]).
      { simpl. auto. }
      apply H in HIn.
      lia.
  - split.
    + intros _.
      exists 10000002.
      split.
      * simpl. auto.
      * lia.
    + intros _. reflexivity.
Qed.