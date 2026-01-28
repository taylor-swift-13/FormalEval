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

Example test_case : sort_third_spec [9; 0; 10; -4; 9; 289; 3; 12; 900; 3] [-4; 0; 10; 3; 9; 289; 3; 12; 900; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Unroll the check for the concrete list length (10 elements) *)
      do 11 (destruct i; [ 
        simpl in *; 
        try reflexivity; 
        try (exfalso; apply H; reflexivity) 
      | ]).
      (* For i >= 10, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-4; 3; 3; 9] [9; -4; 3; 3] *)
        eapply Permutation_trans.
        apply Permutation_swap. (* [-4; 9; 3; 3] *)
        apply Permutation_skip.
        eapply Permutation_trans.
        apply Permutation_swap. (* [9; 3; 3] -> [3; 9; 3] *)
        apply Permutation_skip.
        apply Permutation_swap. (* [9; 3] -> [3; 9] *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat apply Sorted_cons.
        -- apply HdRel_cons. unfold Z.le. simpl. discriminate.
        -- apply HdRel_cons. unfold Z.le. simpl. discriminate.
        -- apply HdRel_cons. unfold Z.le. simpl. discriminate.
        -- apply HdRel_nil.
        -- apply Sorted_nil.
Qed.