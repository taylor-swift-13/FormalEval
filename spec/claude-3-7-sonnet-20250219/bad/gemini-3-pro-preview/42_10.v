Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.Micromega.Lra.
Open Scope R_scope.

Definition incr_list_spec (l res : list R) : Prop :=
  length l = length res /\
  forall i, nth_error res i = 
            match nth_error l i with
            | Some x => Some (x + 1)
            | None => None
            end.

Example test_incr_list_reals: incr_list_spec [0.1; 0.2; 0.3] [1.1; 1.2; 1.3].
Proof.
  unfold incr_list_spec.
  split.
  - simpl. reflexivity.
  - intros i.
    destruct i; simpl.
    + f_equal. lra.
    + destruct i; simpl.
      * f_equal. lra.
      * destruct i; simpl.
        -- f_equal. lra.
        -- reflexivity.
Qed.