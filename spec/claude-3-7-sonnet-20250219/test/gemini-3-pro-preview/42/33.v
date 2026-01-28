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

Example test_incr_list_1: incr_list_spec [1; 1; 1; 1; 10; 1; 1] [2; 2; 2; 2; 11; 2; 2].
Proof.
  unfold incr_list_spec.
  split.
  - simpl.
    reflexivity.
  - intros i.
    repeat (destruct i; simpl; try reflexivity).
Qed.