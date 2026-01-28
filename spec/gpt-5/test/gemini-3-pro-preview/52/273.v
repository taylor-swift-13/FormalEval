Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 125; 6; 62; 31; 31] 499 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* We must show that Forall (...) leads to a contradiction because 1000 >= 499 *)
      rewrite Forall_forall in H.
      specialize (H 1000).
      assert (In 1000 [1000; 500; 250; 125; 6; 62; 31; 31]).
      { simpl. left. reflexivity. }
      apply H in H0.
      lia.
  - (* res = false <-> exists ... *)
    split.
    + intros _.
      exists 1000.
      split.
      * simpl. left. reflexivity.
      * lia.
    + intros _.
      reflexivity.
Qed.