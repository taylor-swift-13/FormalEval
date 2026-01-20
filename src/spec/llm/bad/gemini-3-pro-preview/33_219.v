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
  [1; 2; 3; -3; 2; 1; 0; -8; 9; -12; 7; 6] 
  [-12; 2; 3; -3; 2; 1; 0; -8; 9; 1; 7; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for each index 0..11 and beyond *)
      do 13 (destruct i as [|i]; [ simpl in *; try (contradiction || reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-12; -3; 0; 1] [1; -3; 0; -12] *)
        apply Permutation_sym.
        (* Goal: Permutation [1; -3; 0; -12] [-12; -3; 0; 1] *)
        apply Permutation_trans with (l' := -12 :: [1; -3; 0]).
        { 
          change [1; -3; 0; -12] with ([1; -3; 0] ++ [-12]).
          apply Permutation_sym. apply Permutation_cons_app. 
        }
        {
          apply Permutation_cons.
          apply Permutation_trans with (l' := -3 :: [1; 0]).
          {
            change [1; -3; 0] with ([1] ++ [-3] ++ [0]).
            apply Permutation_sym. apply Permutation_cons_app.
          }
          {
            apply Permutation_cons.
            apply Permutation_swap.
          }
        }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        -- apply HdRel_cons. simpl. lia.
        -- apply Sorted_cons.
           ++ apply HdRel_cons. simpl. lia.
           ++ apply Sorted_cons.
              ** apply HdRel_cons. simpl. lia.
              ** apply Sorted_nil.
Qed.