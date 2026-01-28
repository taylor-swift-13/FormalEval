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
  [5; 2; -13; 3; -5; 2; -10; -3; -2; -2; 3; 2; -8; 0; -10; -9; -10; 3] 
  [-13; 2; -10; 3; -10; 2; -10; -3; -8; -2; -5; 2; -2; 0; 3; -9; 5; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate Hodd; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Step 1: Move -13 to head *)
        transitivity (-13 :: [5] ++ [-5; -10; -2; 3; -8; -10; -10]).
        2: apply perm_skip.
        change [5; -13; -5; -10; -2; 3; -8; -10; -10] with ([5] ++ -13 :: [-5; -10; -2; 3; -8; -10; -10]).
        apply Permutation_sym. apply Permutation_middle.
        
        (* Step 2: Move -10 to head *)
        transitivity (-10 :: [5; -5] ++ [-2; 3; -8; -10; -10]).
        2: apply perm_skip.
        change [5; -5; -10; -2; 3; -8; -10; -10] with ([5; -5] ++ -10 :: [-2; 3; -8; -10; -10]).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 3: Move -10 to head *)
        transitivity (-10 :: [5; -5; -2; 3; -8] ++ [-10]).
        2: apply perm_skip.
        change [5; -5; -2; 3; -8; -10; -10] with ([5; -5; -2; 3; -8] ++ -10 :: [-10]).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 4: Move -10 to head *)
        transitivity (-10 :: [5; -5; -2; 3; -8] ++ []).
        2: apply perm_skip.
        change [5; -5; -2; 3; -8; -10] with ([5; -5; -2; 3; -8] ++ -10 :: []).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 5: Move -8 to head *)
        transitivity (-8 :: [5; -5; -2; 3] ++ []).
        2: apply perm_skip.
        change [5; -5; -2; 3; -8] with ([5; -5; -2; 3] ++ -8 :: []).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 6: Move -5 to head *)
        transitivity (-5 :: [5] ++ [-2; 3]).
        2: apply perm_skip.
        change [5; -5; -2; 3] with ([5] ++ -5 :: [-2; 3]).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 7: Move -2 to head *)
        transitivity (-2 :: [5] ++ [3]).
        2: apply perm_skip.
        change [5; -2; 3] with ([5] ++ -2 :: [3]).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 8: Move 3 to head *)
        transitivity (3 :: [5] ++ []).
        2: apply perm_skip.
        change [5; 3] with ([5] ++ 3 :: []).
        apply Permutation_sym. apply Permutation_middle.

        (* Step 9: Final element 5 *)
        apply perm_skip. apply perm_nil.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.