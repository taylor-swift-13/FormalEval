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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 200; 3; 0; 5; 700; 900; 18; -901; 800; 1000; 0; 289; -277; 18; -277]
  [-277; 500; 6; 5; 8; 289; 7; -105; -277; 18; 3; 0; 20; 700; 900; 200; -901; 800; 300; 0; 289; 1000; 18; -277].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 24 (destruct i; [ simpl in *; try (elim H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-277 :: [300; 7; 20; 200; 5; 18; 1000]).
        { apply Permutation_sym. 
          change ([300; 7; 20; 200; 5; 18; 1000; -277]) with ([300; 7; 20; 200; 5; 18; 1000] ++ [-277]).
          apply Permutation_middle. }
        apply perm_skip.
        transitivity (5 :: [300; 7; 20; 200; 18; 1000]).
        { apply Permutation_sym.
          change ([300; 7; 20; 200; 5; 18; 1000]) with ([300; 7; 20; 200] ++ 5 :: [18; 1000]).
          apply Permutation_middle. }
        apply perm_skip.
        transitivity (7 :: [300; 20; 200; 18; 1000]).
        { apply Permutation_sym.
          change ([300; 7; 20; 200; 18; 1000]) with ([300] ++ 7 :: [20; 200; 18; 1000]).
          apply Permutation_middle. }
        apply perm_skip.
        transitivity (18 :: [300; 20; 200; 1000]).
        { apply Permutation_sym.
          change ([300; 20; 200; 18; 1000]) with ([300; 20; 200] ++ 18 :: [1000]).
          apply Permutation_middle. }
        apply perm_skip.
        transitivity (20 :: [300; 200; 1000]).
        { apply Permutation_sym.
          change ([300; 20; 200; 1000]) with ([300] ++ 20 :: [200; 1000]).
          apply Permutation_middle. }
        apply perm_skip.
        transitivity (200 :: [300; 1000]).
        { apply Permutation_sym.
          change ([300; 200; 1000]) with ([300] ++ 200 :: [1000]).
          apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat constructor.
        all: unfold Z.le; simpl; discriminate.
Qed.