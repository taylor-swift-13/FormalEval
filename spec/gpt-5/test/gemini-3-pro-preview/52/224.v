Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 20; -30; 40; -50] 12 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      assert (Hin : In 20 [10; 20; -30; 40; -50]) by (simpl; tauto).
      rewrite Forall_forall in H.
      apply H in Hin.
      lia.
  - split.
    + intros _.
      exists 20.
      split.
      * simpl. tauto.
      * lia.
    + intros _. reflexivity.
Qed.