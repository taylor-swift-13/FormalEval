Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition incr_list_spec (l res : list nat) : Prop :=
  length l = length res /\
  forall i, nth_error res i = 
            match nth_error l i with
            | Some x => Some (x + 1)
            | None => None
            end.

Example incr_list_spec_empty: incr_list_spec [] [].
Proof.
  unfold incr_list_spec.
  split.
  - simpl. reflexivity.
  - intros i.
    assert (Hnil : nth_error ([] : list nat) i = None).
    { apply nth_error_None. simpl. lia. }
    rewrite Hnil. simpl. reflexivity.
Qed.