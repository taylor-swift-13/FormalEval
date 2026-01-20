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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 9; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 1000] 
  [-104; 500; 6; 3; 8; 289; 7; -105; -277; 9; 104; 200; 20; 4; 5; 300; 900; -200; 700; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -104 :: [300; 7; 20; 9; 3; 700] ++ [1000]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [300; 7; 20; 9; 3; 700]) (l2 := [1000]). }
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := 3 :: [300; 7; 20; 9] ++ [700; 1000]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [300; 7; 20; 9]) (l2 := [700; 1000]). }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 7 :: [300] ++ [20; 9; 700; 1000]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [300]) (l2 := [20; 9; 700; 1000]). }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 9 :: [300; 20] ++ [700; 1000]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [300; 20]) (l2 := [700; 1000]). }
        apply Permutation_cons.

        apply Permutation_trans with (l' := 20 :: [300] ++ [700; 1000]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [300]) (l2 := [700; 1000]). }
        apply Permutation_cons.

        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.