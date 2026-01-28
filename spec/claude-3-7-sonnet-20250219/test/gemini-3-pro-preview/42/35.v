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

Example test_incr_list: incr_list_spec [-1; -5; -3; -5; -3; -3] [0; -4; -2; -4; -2; -2].
Proof.
  unfold incr_list_spec.
  split.
  - simpl.
    reflexivity.
  - intros i.
    do 7 (destruct i; try (simpl; reflexivity)).
Qed.