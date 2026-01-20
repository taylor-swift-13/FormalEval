Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.

Definition incr_list_spec (l res : list nat) : Prop :=
  length l = length res /\
  forall i, nth_error res i = 
            match nth_error l i with
            | Some x => Some (x + 1)
            | None => None
            end.

Example test_incr_list_empty : incr_list_spec [] [].
Proof.
  unfold incr_list_spec.
  split.
  - (* Prove length [] = length [] *)
    simpl.
    reflexivity.
  - (* Prove nth_error relationship *)
    intros i.
    (* nth_error [] i does not reduce automatically because nth_error is recursive on the index.
       Destructing i forces the evaluation. *)
    destruct i.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.