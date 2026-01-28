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
  [3; 3; 2; 0; 2; 1; 11; 1; 4; 3; 2] 
  [2; 3; 2; 0; 2; 1; 3; 1; 4; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* LHS: [3; 2; 2; 11; 4; 2], RHS: [2; 2; 2; 3; 4; 11] *)
        apply perm_trans with (2 :: 3 :: 2 :: 11 :: 4 :: 2 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (2 :: 3 :: 11 :: 4 :: 2 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (3 :: 11 :: 2 :: 4 :: []).
        { repeat apply perm_skip. apply perm_swap. }
        apply perm_trans with (3 :: 2 :: 11 :: 4 :: []).
        { apply perm_skip. apply perm_swap. }
        apply perm_trans with (2 :: 3 :: 11 :: 4 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.