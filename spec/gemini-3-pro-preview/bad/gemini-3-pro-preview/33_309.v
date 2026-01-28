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
  [1; 2; 3; -3; 5; 1; 16; -8; 9; -12; 7; 4; -12; 7; 7; 4] 
  [-12; 2; 3; -12; 5; 1; -3; -8; 9; 1; 7; 4; 4; 7; 7; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity (-12 :: [1; -3; 16] ++ [-12; 4]).
        { constructor.
          transitivity (-12 :: [1; -3; 16] ++ [4]).
          { constructor.
            transitivity (-3 :: [1] ++ [16; 4]).
            { constructor.
              constructor.
              transitivity (4 :: [16] ++ []).
              { repeat constructor. }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * simpl.
        repeat (constructor; try (compute; discriminate)).
Qed.