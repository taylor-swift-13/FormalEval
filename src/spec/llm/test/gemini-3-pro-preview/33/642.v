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
  [500; 6; 7; 290; 3; 8; 289; 20; 104; -277; 104; 200; 3; 4; -8; 700; -2; -901; 800; 1000]
  [-277; 6; 7; 3; 3; 8; 289; 20; 104; 290; 104; 200; 500; 4; -8; 700; -2; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -277 :: [500; 290; 289; 3; 700; 800]).
        { constructor.
          apply Permutation_trans with (l' := 3 :: [500; 290; 289; 700; 800]).
          { constructor.
            apply Permutation_trans with (l' := 289 :: [500; 290; 700; 800]).
            { constructor.
              apply Permutation_trans with (l' := 290 :: [500; 700; 800]).
              { constructor. apply Permutation_refl. }
              { apply Permutation_middle with (l1 := [500]). }
            }
            { apply Permutation_middle with (l1 := [500; 290]). }
          }
          { apply Permutation_middle with (l1 := [500; 290; 289]). }
        }
        { apply Permutation_middle with (l1 := [500; 290; 289]). }
      * simpl.
        repeat (constructor || (compute; discriminate)).
Qed.