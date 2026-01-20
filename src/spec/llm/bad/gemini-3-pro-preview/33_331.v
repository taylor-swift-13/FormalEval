Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [-4; 7; 3; -6; 3; -8; -7; 2; 0; 1; 8; 0] 
  [-7; 7; 3; -6; 3; -8; -4; 2; 0; 1; 8; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* length res = length l *)
    simpl. reflexivity.
  - split.
    + (* Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check indices 0 to 11 explicitly *)
      do 12 (destruct i; [
        (* i = 0..11 *)
        simpl in H;
        (* If i mod 3 = 0, H is contradictory *)
        try (exfalso; apply H; reflexivity);
        (* If i mod 3 <> 0, check that nth_error matches *)
        simpl; reflexivity
      | ]).
      (* For i >= 12, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        simpl.
        (* We need to show Permutation [-7; -6; -4; 1] [-4; -6; -7; 1] *)
        eapply Permutation_trans.
        2: apply Permutation_swap. (* Swaps -4 and -6 in RHS -> [-6; -4; -7; 1] *)
        eapply Permutation_trans.
        2: { apply perm_skip. apply Permutation_swap. } (* Swaps -4 and -7 in tail -> [-6; -7; -4; 1] *)
        apply Permutation_swap. (* Swaps -6 and -7 in head -> [-7; -6; -4; 1] *)
      * (* Sortedness of extracted thirds *)
        simpl.
        (* List is [-7; -6; -4; 1] *)
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. apply Z.leb_le. reflexivity. } } (* -4 <= 1 *)
          { apply HdRel_cons. apply Z.leb_le. reflexivity. } } (* -6 <= -4 *)
        { apply HdRel_cons. apply Z.leb_le. reflexivity. } (* -7 <= -6 *)
Qed.