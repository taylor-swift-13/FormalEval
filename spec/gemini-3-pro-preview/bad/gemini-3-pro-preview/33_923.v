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

Example test_case : sort_third_spec [9; -5; 29; -276; -6; 9; -6] [-276; -5; 29; -6; -6; 9; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check indices 0 to 7. For i >= 8, both are None. *)
      do 8 (destruct i; [
        (* Check if i mod 3 == 0, if so H is false. Else check value equality *)
        try (exfalso; compute in H; discriminate H);
        simpl; reflexivity
      | ]).
      (* Case i >= 8 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-276; -6; 9] [9; -276; -6] *)
        eapply perm_trans.
        2: apply perm_swap. (* Swaps 9 and -276 in the RHS to match head of LHS *)
        apply perm_skip.    (* Matches -276 *)
        apply perm_swap.    (* Swaps 9 and -6 *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-276; -6; 9] *)
        apply Sorted_cons.
        -- unfold HdRel. simpl. unfold Z.le. simpl. discriminate.
        -- apply Sorted_cons.
           ++ unfold HdRel. simpl. unfold Z.le. simpl. discriminate.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
Qed.