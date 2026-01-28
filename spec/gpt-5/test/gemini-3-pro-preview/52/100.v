Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 20; -30; 40; -50] 15 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* Prove that Forall implies a contradiction because 20 >= 15 *)
      inversion H; subst. (* 10 < 15 *)
      inversion H3; subst. (* 20 < 15, contradiction *)
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Provide a witness x that is In l and >= 15 *)
      exists 20.
      split.
      * simpl. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.