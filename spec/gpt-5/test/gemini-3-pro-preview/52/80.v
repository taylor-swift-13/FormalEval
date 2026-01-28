Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1; 0; 2; 0; 0] 2 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      discriminate H.
    + intros H.
      assert (HIn : In 2 [1; 0; 2; 0; 0]).
      { simpl. right. right. left. reflexivity. }
      rewrite Forall_forall in H.
      apply H in HIn.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 2.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _.
      reflexivity.
Qed.