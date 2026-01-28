Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 2; 3; -1; 4; 4] 4 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      assert (In 4 [1; 2; 3; -1; 4; 4]).
      { simpl. right. right. right. right. left. reflexivity. }
      apply H in H0. lia.
  - split.
    + intros _.
      exists 4.
      split.
      * simpl. right. right. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.