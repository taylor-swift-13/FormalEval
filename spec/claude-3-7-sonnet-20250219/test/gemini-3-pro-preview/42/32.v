Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition incr_list_spec (l res : list Z) : Prop :=
  length l = length res /\
  forall i, nth_error res i = 
            match nth_error l i with
            | Some x => Some (x + 1)
            | None => None
            end.

Example test_incr_list_1: incr_list_spec [-10; 0; 10; 0; 0] [-9; 1; 11; 1; 1].
Proof.
  unfold incr_list_spec.
  split.
  - simpl. reflexivity.
  - intros i.
    repeat (destruct i; simpl; try reflexivity).
Qed.