Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [-200; 300; 8000000; -400; -600; 300] 1001 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate.
    + intros H.
      rewrite Forall_forall in H.
      specialize (H 8000000).
      assert (In 8000000 [-200; 300; 8000000; -400; -600; 300]) as HIn.
      { simpl. right. right. left. reflexivity. }
      apply H in HIn.
      lia.
  - split.
    + intros _.
      exists 8000000.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.