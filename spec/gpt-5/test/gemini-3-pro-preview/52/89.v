Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [-3; -2; 4; 4; -2] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      assert (In 4 [-3; -2; 4; 4; -2]) by (simpl; auto).
      apply H in H0.
      lia.
  - split.
    + intros _.
      exists 4.
      split.
      * simpl. auto.
      * lia.
    + intros _. reflexivity.
Qed.