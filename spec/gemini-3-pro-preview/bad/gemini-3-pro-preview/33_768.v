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
  [-4; 7; 3; 290; 3; 0; -8; 6; 2; 0; 8; 2; 7; 7] 
  [-8; 7; 3; -4; 3; 0; 0; 6; 2; 7; 8; 2; 290; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      (* Check i = 0 to 13 *)
      do 14 (destruct i; [ 
        simpl; try reflexivity; try (exfalso; compute in H; discriminate) | ]).
      (* i >= 14 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* Goal: Permutation [-8; -4; 0; 7; 290] [-4; 290; -8; 0; 7] *)
        transitivity (-8 :: [-4; 290; 0; 7]).
        { apply Permutation_cons.
          apply Permutation_cons.
          transitivity (0 :: [290; 7]).
          { apply Permutation_cons. apply Permutation_swap. }
          { change [290; 0; 7] with ([290] ++ 0 :: [7]).
            apply Permutation_middle. }
        }
        { change [-4; 290; -8; 0; 7] with ([-4; 290] ++ -8 :: [0; 7]).
          apply Permutation_middle. }
      * (* 4. Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; red; simpl; intro H; discriminate) ]).
        apply Sorted_nil.
Qed.