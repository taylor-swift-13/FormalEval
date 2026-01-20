Existing Coq output file content specification for the new test case `input = [[3%Z; 3%Z; 2%Z; 8%Z; 2%Z; 2%Z; 11%Z; 0%Z; 1%Z; 3%Z; 0%Z; 11%Z]], output = [0%Z; 3%Z; 1%Z; 8%Z; 2%Z; 2%Z; 2%Z; 0%Z; 3%Z; 3%Z; 11%Z; 11%Z]`:

```coq
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
  [3; 3; 2; 8; 2; 2; 11; 0; 1; 3; 0; 11] 
  [0; 3; 1; 8; 2; 2; 2; 0; 3; 3; 11; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [
        simpl in Hodd; try discriminate; simpl; reflexivity
      | simpl in Hlen ]).
      lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [3; 2; 2; 11; 1; 0] [0; 1; 2; 2; 3; 11] *)
        transitivity (0 :: [3; 2; 2; 11; 1]).
        { apply Permutation_sym.
          change (3 :: 2 :: 2 :: 11 :: 1 :: 0 :: nil) with ([3; 2; 2; 11; 1] ++ 0 :: nil).
          apply Permutation_middle. }
        apply Permutation_cons.
        (* Goal: Permutation [3; 2; 2; 11; 1] [1; 2; 2; 3; 11] *)
        transitivity (1 :: [3; 2; 2; 11]).
        { apply Permutation_sym.
          change (3 :: 2 :: 2 :: 11 :: 1 :: nil) with ([3; 2; 2; 11] ++ 1 :: nil).
          apply Permutation_middle. }
        apply Permutation_cons.
        (* Goal: Permutation [3; 2; 2; 11] [2; 2; 3; 11] *)
        transitivity (2 :: [3; 2; 11]).
        { apply Permutation_sym.
          change (3 :: 2 :: 2 :: 11 :: nil) with ([3] ++ 2 :: [2; 11]).
          apply Permutation_middle. }
        apply Permutation_cons.
        (* Goal: Permutation [3; 2; 11] [2; 3; 11] *)
        apply perm_swap.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.