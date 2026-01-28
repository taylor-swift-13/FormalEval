Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [4; -4; 7; 10] 6 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* true = false is impossible *)
      discriminate H.
    + intros H.
      (* Prove contradiction: Forall implies 7 < 6 *)
      inversion H; subst.
      inversion H3; subst.
      inversion H5; subst.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Witness 7 satisfies the condition *)
      exists 7.
      split.
      * simpl. auto.
      * lia.
    + intros _.
      reflexivity.
Qed.