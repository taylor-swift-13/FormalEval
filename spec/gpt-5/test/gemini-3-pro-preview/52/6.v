Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 8; 4; 10] 10 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      rewrite Forall_forall in H.
      specialize (H 10).
      assert (In 10 [1; 8; 4; 10]) by (simpl; lia).
      apply H in H0.
      lia.
  - split.
    + intros _.
      exists 10.
      split.
      * simpl; lia.
      * lia.
    + intros _. reflexivity.
Qed.