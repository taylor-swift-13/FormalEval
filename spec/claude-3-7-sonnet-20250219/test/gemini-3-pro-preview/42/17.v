Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition incr_list_spec (l res : list Z) : Prop :=
  length l = length res /\
  forall i, nth_error res i = 
            match nth_error l i with
            | Some x => Some (x + 1)
            | None => None
            end.

Example test_incr_list_basic: incr_list_spec [-1; -5; -3; -5; -3] [0; -4; -2; -4; -2].
Proof.
  unfold incr_list_spec.
  split.
  - simpl. reflexivity.
  - intros i.
    do 5 (destruct i; [simpl; reflexivity | ]).
    destruct i; simpl; reflexivity.
Qed.