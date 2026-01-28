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

Example test_incr_list_basic: incr_list_spec [2; 200; 2; 2; 2] [3; 201; 3; 3; 3].
Proof.
  unfold incr_list_spec.
  split.
  - simpl.
    reflexivity.
  - intros i.
    repeat (destruct i; try (simpl; reflexivity)).
Qed.