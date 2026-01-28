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
  [5; 123; 3; 7; 0; 2; -3; -10; 0; 123; 1; 0; -10; 123] 
  [-10; 123; -3; 7; 0; 2; 0; -10; 1; 123; 3; 0; 5; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_sym.
        (* Goal: Permutation [-10; -3; 0; 0; 1; 3; 5] [5; 3; 0; -3; 0; 1; -10] *)
        transitivity (-10 :: [5; 3; 0; -3; 0; 1] ++ []).
        { apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Goal: Permutation [-3; 0; 0; 1; 3; 5] [5; 3; 0; -3; 0; 1] *)
        transitivity (-3 :: [5; 3; 0] ++ [0; 1]).
        { apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Goal: Permutation [0; 0; 1; 3; 5] [5; 3; 0; 0; 1] *)
        transitivity (0 :: [5; 3] ++ [0; 1]).
        { apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Goal: Permutation [0; 1; 3; 5] [5; 3; 0; 1] *)
        transitivity (0 :: [5; 3] ++ [1]).
        { apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Goal: Permutation [1; 3; 5] [5; 3; 1] *)
        transitivity (1 :: [5; 3] ++ []).
        { apply Permutation_middle. }
        apply perm_skip.
        simpl.
        
        (* Goal: Permutation [3; 5] [5; 3] *)
        apply perm_swap.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil); try lia.
Qed.