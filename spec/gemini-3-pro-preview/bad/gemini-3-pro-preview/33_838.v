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
  [6; 2; 7; 9; 15; 3; 7; -7; 11; 8; 0; 13; 6; -2; 19; 5; 15; 5] 
  [5; 2; 7; 6; 15; 3; 6; -7; 11; 7; 0; 13; 8; -2; 19; 9; 15; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (5 :: [6; 9; 7; 8; 6]).
        { apply Permutation_cons. 
          apply Permutation_cons.
          apply Permutation_trans with (6 :: [9; 7; 8]).
          { apply Permutation_cons.
            apply Permutation_trans with (7 :: [9; 8]).
            { apply Permutation_cons.
              apply Permutation_trans with (8 :: [9]).
              { apply Permutation_cons. apply Permutation_refl. }
              { apply Permutation_sym. change [9; 8] with ([9] ++ 8 :: []). apply Permutation_middle. }
            }
            { apply Permutation_sym. change [9; 7; 8] with ([9] ++ 7 :: [8]). apply Permutation_middle. }
          }
          { apply Permutation_sym. change [9; 7; 8; 6] with ([9; 7; 8] ++ 6 :: []). apply Permutation_middle. }
        }
        { apply Permutation_sym. change [6; 9; 7; 8; 6; 5] with ([6; 9; 7; 8; 6] ++ 5 :: []). apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ try apply HdRel_nil; try (apply HdRel_cons; vm_compute; discriminate) | ]).
        apply Sorted_nil.
Qed.