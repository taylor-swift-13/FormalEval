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
  [-4; 8; 4; -6; 0; -8; 6; 2; 1; 13; 6; 6; -8; 14; -6; 8] 
  [-8; 8; 4; -6; 0; -8; -4; 2; 1; 6; 6; 6; 8; 14; -6; 13].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We perform case analysis on i for the length of the list (16 elements) *)
      do 17 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      (* Case i >= 16 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-8; -6; -4; 6; 8; 13] [-4; -6; 6; 13; -8; 8] *)
        apply Permutation_trans with (l' := -8 :: ([-4; -6; 6; 13] ++ [8])).
        { apply Permutation_cons. simpl.
          (* Goal: Permutation [-6; -4; 6; 8; 13] [-4; -6; 6; 13; 8] *)
          apply Permutation_trans with (l' := -6 :: ([-4] ++ [6; 13; 8])).
          { apply Permutation_cons. simpl.
            (* Goal: Permutation [-4; 6; 8; 13] [-4; 6; 13; 8] *)
            apply Permutation_cons.
            (* Goal: Permutation [6; 8; 13] [6; 13; 8] *)
            apply Permutation_cons.
            (* Goal: Permutation [8; 13] [13; 8] *)
            apply Permutation_swap.
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | constructor; try (compute; congruence) ]).
        apply Sorted_nil.
Qed.