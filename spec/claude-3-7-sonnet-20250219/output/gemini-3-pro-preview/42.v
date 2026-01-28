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

Example test_incr_list_empty: incr_list_spec [] [].
Proof.
  unfold incr_list_spec.
  split.
  - (* Prove length [] = length [] *)
    simpl.
    reflexivity.
  - (* Prove nth_error correspondence *)
    intros i.
    (* nth_error is defined by recursion on the index, so we destruct i *)
    destruct i; simpl; reflexivity.
Qed.