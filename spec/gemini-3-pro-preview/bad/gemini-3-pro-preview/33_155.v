Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
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
  [1; 2; 3; -3; 5; 1; 16; 16; -8; 9; -12; 7; 6; -12; 16] 
  [-3; 2; 3; 1; 5; 1; 6; 16; -8; 9; -12; 7; 16; -12; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        transitivity ((-3) :: 1 :: 16 :: 9 :: 6 :: nil).
        { apply Permutation_cons. apply Permutation_cons.
          transitivity (9 :: 16 :: 6 :: nil).
          { transitivity (9 :: 6 :: 16 :: nil).
            { apply Permutation_swap. }
            { apply Permutation_cons. apply Permutation_swap. } 
          }
          { apply Permutation_swap. } 
        }
        { apply Permutation_swap. }
      * simpl.
        repeat (constructor; try lia).
Qed.