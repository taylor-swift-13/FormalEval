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
  [500; 6; 7; 8; 288; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 801; 1000; -277; 7] 
  [-200; 6; 7; -105; 288; 20; 5; -277; 104; 8; 3; 4; 200; 700; 900; 500; -901; 801; 1000; -277; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [ simpl in *; try (elim H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        transitivity (-200 :: [500; 8; -105; 200; 5] ++ [1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        transitivity (-105 :: [500; 8] ++ [200; 5; 1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        transitivity (5 :: [500; 8; 200] ++ [1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        transitivity (8 :: [500] ++ [200; 1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        transitivity (200 :: [500] ++ [1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        transitivity (500 :: [] ++ [1000]).
        { apply Permutation_sym, Permutation_middle. }
        constructor. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ simpl; try apply HdRel_nil; apply HdRel_cons; apply Z.leb_le; reflexivity | ]).
        apply Sorted_nil.
Qed.