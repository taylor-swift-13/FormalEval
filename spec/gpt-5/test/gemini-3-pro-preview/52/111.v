Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [10; 20; -30; 40; -50] 20 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove that Forall implies a contradiction because 20 is not < 20 *)
      inversion H as [|x l' Hlt Hrest]; subst. (* 10 < 20 *)
      inversion Hrest as [|x2 l2 Hlt2 Hrest2]; subst. (* 20 < 20 *)
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Provide the witness that violates the threshold *)
      exists 20.
      split.
      * simpl. auto.
      * lia.
    + intros _.
      reflexivity.
Qed.