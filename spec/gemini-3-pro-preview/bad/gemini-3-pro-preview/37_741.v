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
  [1; 5; 3; -5; 23; -3; 3; -9; 0; 123; -1; -10] 
  [-1; 5; 0; -5; 1; -3; 3; -9; 3; 123; 23; -10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 11 explicitly *)
      do 12 (destruct i as [|i]; 
             [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) 
             | ]).
      (* Handle out of bounds indices *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 3; 23; 3; 0; -1] [-1; 0; 1; 3; 3; 23] *)
        
        (* Move -1 to the front *)
        transitivity (-1 :: [1; 3; 23; 3; 0]).
        { change [1; 3; 23; 3; 0; -1] with ([1; 3; 23; 3; 0] ++ [-1]).
          apply Permutation_app_comm. }
        apply perm_skip.
        
        (* Move 0 to the front *)
        transitivity (0 :: [1; 3; 23; 3]).
        { change [1; 3; 23; 3; 0] with ([1; 3; 23; 3] ++ [0]).
          apply Permutation_app_comm. }
        apply perm_skip.
        
        (* 1 is already at the front *)
        apply perm_skip.
        
        (* 3 is already at the front *)
        apply perm_skip.
        
        (* Swap 23 and 3 to match [3; 23] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.