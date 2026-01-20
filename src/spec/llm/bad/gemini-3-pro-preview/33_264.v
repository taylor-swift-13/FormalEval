Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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

Definition input := [19; 0; 2; 4; 3; 4; 5; 6; 7; -9; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 11; 16].
Definition output := [-9; 0; 2; 4; 3; 4; 5; 6; 7; 11; 9; 10; 14; 12; 13; 17; 15; 16; 19; 18; 19; 20; 11; 16].

Example test_case : sort_third_spec input output.
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 24 (destruct i as [|i]; [
        compute in H; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * compute.
        apply Permutation_sym.
        transitivity (19 :: 4 :: -9 :: 5 :: [11; 14; 17; 20]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        transitivity (19 :: -9 :: 4 :: 5 :: [11; 14; 17; 20]).
        { apply perm_skip. apply perm_swap. }
        transitivity (-9 :: 19 :: 4 :: 5 :: [11; 14; 17; 20]).
        { apply perm_swap. }
        apply perm_skip.
        change [4; 5; 11; 14; 17; 19; 20] with ([4; 5; 11; 14; 17] ++ 19 :: [20]).
        apply Permutation_middle.
      * compute.
        repeat (apply Sorted_cons; [ try apply HdRel_cons; try apply HdRel_nil; try lia | ]).
        apply Sorted_nil.
Qed.