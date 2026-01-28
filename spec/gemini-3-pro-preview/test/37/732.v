Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [2; 3; 2; 9; 3; 6; 7; 8; 9; 2; 2; 3; 3] 
  [2; 3; 2; 9; 2; 6; 3; 8; 3; 2; 7; 3; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons; [reflexivity|].
        apply Permutation_cons; [reflexivity|].
        transitivity (3 :: 2 :: 3 :: 7 :: 9 :: []).
        { apply Permutation_cons; [reflexivity|].
          transitivity (7 :: 2 :: 3 :: 9 :: []).
          { apply Permutation_cons; [reflexivity|].
            transitivity (9 :: 2 :: 3 :: []).
            { apply Permutation_cons; [reflexivity|].
              apply Permutation_refl. }
            { transitivity (2 :: 9 :: 3 :: []).
              - apply perm_swap.
              - apply Permutation_cons; [reflexivity|]. apply perm_swap. }
          }
          { transitivity (2 :: 7 :: 3 :: 9 :: []).
            - apply perm_swap.
            - apply Permutation_cons; [reflexivity|]. apply perm_swap. }
        }
        { apply perm_swap. }
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.