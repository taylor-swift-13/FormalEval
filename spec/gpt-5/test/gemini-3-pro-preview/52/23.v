Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [-4; -3; -2; -1] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      assert (In (-1) [-4; -3; -2; -1]).
      { simpl. do 3 right. left. reflexivity. }
      apply H in H0. lia.
  - split.
    + intros _.
      exists (-1).
      split.
      * simpl. do 3 right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.