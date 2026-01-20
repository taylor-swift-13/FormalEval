Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 7; 3; 12; 4; 5; 700; 900; -901; 800; 1000]
  [-901; 500; 6; 3; 8; 289; 5; -105; -277; 7; 8; 7; 20; 12; 4; 104; 700; 900; 300; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -901 :: [300; 7; 20; 104; 3; 5] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (l' := 3 :: [300; 7; 20; 104] ++ [5]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (l' := 5 :: [300; 7; 20; 104] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (l' := 7 :: [300] ++ [20; 104]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (l' := 20 :: [300] ++ [104]).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_trans with (l' := 104 :: [300] ++ []).
        2: apply Permutation_middle.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.