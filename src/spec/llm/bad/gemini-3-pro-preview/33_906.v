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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -276; 104; 200; 3; 4; 700; 800; 1000; -901; 1000]
  [-276; 500; 6; 3; 290; 8; 7; 20; -105; 289; 104; 200; 300; 4; 700; 800; 1000; -901; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * vm_compute.
        transitivity (-276 :: [300; 7; 289; 3; 800; 1000]).
        apply perm_skip.
        change [300; 7; 289; -276; 3; 800; 1000] with ([300; 7; 289] ++ -276 :: [3; 800; 1000]).
        apply Permutation_middle.
        
        transitivity (3 :: [300; 7; 289; 800; 1000]).
        apply perm_skip.
        change [300; 7; 289; 3; 800; 1000] with ([300; 7; 289] ++ 3 :: [800; 1000]).
        apply Permutation_middle.

        transitivity (7 :: [300; 289; 800; 1000]).
        apply perm_skip.
        change [300; 7; 289; 800; 1000] with ([300] ++ 7 :: [289; 800; 1000]).
        apply Permutation_middle.

        transitivity (289 :: [300; 800; 1000]).
        apply perm_skip.
        change [300; 289; 800; 1000] with ([300] ++ 289 :: [800; 1000]).
        apply Permutation_middle.

        transitivity (300 :: [800; 1000]).
        apply perm_skip.
        change [300; 800; 1000] with ([] ++ 300 :: [800; 1000]).
        apply Permutation_middle.

        apply Permutation_refl.
      * vm_compute.
        repeat (apply Sorted_cons; [ red; simpl; intro H; discriminate | ]).
        apply Sorted_nil.
Qed.