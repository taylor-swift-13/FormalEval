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

Example test_sort_even_case : sort_even_spec [5; 0; 6; 0; 5; -12; 0; -5; 3; -5] [0; 0; 3; 0; 5; -12; 5; -5; 6; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (0 :: [5; 6; 5; 3]).
        { change [5; 6; 5; 0; 3] with ([5; 6; 5] ++ 0 :: [3]). apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        transitivity (3 :: [5; 6; 5]).
        { change [5; 6; 5; 3] with ([5; 6; 5] ++ 3 :: []). apply Permutation_sym. apply Permutation_middle. }
        simpl. apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.