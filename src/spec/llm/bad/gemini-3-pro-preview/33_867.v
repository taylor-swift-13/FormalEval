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
  [5; 2; 7; -1; 9; 0; 3; -6; 9; 11; 8; -6; 0; 300; 13; 6; -2; 19]
  [-1; 2; 7; 0; 9; 0; 3; -6; 9; 5; 8; -6; 6; 300; 13; 11; -2; 19].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 18 (destruct i; [
        simpl in *; try contradiction; reflexivity |
      ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        apply Permutation_trans with (l' := -1 :: [5; 3; 11; 0; 6]).
        { apply Permutation_cons.
          apply Permutation_trans with (l' := 0 :: [5; 3; 11; 6]).
          { apply Permutation_cons.
            apply Permutation_trans with (l' := 3 :: [5; 11; 6]).
            { apply Permutation_cons.
              apply Permutation_cons.
              apply Permutation_trans with (l' := 6 :: [11]).
              { apply Permutation_cons. apply Permutation_refl. }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * vm_compute.
        repeat (constructor; try (apply Z.leb_le; reflexivity)).
Qed.