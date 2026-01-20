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
  [5; 2; -13; 3; -5; 2; -10; -3; -2; 3; -8; 0; -5; -10; -9; 3] 
  [-13; 2; -10; 3; -9; 2; -8; -3; -5; 3; -5; 0; -2; -10; 5; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 16 (destruct i; [ simpl; try reflexivity; try discriminate | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -13; -5; -10; -2; -8; -5; -9] [-13; -10; -9; -8; -5; -5; -2; 5] *)
        (* Move 5 to the end of RHS to match LHS head *)
        change [-13; -10; -9; -8; -5; -5; -2; 5] with ([-13; -10; -9; -8; -5; -5; -2] ++ 5 :: []).
        apply Permutation_trans with (l' := 5 :: ([-13; -10; -9; -8; -5; -5; -2] ++ [])).
        -- apply perm_skip.
           (* Goal: Permutation [-13; -5; -10; -2; -8; -5; -9] [-13; -10; -9; -8; -5; -5; -2] *)
           apply perm_skip.
           (* Goal: Permutation [-5; -10; -2; -8; -5; -9] [-10; -9; -8; -5; -5; -2] *)
           (* Move -5 to match LHS head *)
           change [-10; -9; -8; -5; -5; -2] with ([-10; -9; -8] ++ -5 :: [-5; -2]).
           apply Permutation_trans with (l' := -5 :: ([-10; -9; -8] ++ [-5; -2])).
           ++ apply perm_skip.
              (* Goal: Permutation [-10; -2; -8; -5; -9] ([-10; -9; -8] ++ [-5; -2]) *)
              simpl.
              (* Goal: Permutation [-10; -2; -8; -5; -9] [-10; -9; -8; -5; -2] *)
              apply perm_skip.
              (* Goal: Permutation [-2; -8; -5; -9] [-9; -8; -5; -2] *)
              (* Move -2 to match LHS head *)
              change [-9; -8; -5; -2] with ([-9; -8; -5] ++ -2 :: []).
              apply Permutation_trans with (l' := -2 :: ([-9; -8; -5] ++ [])).
              ** apply perm_skip.
                 (* Goal: Permutation [-8; -5; -9] [-9; -8; -5] *)
                 (* Move -8 to match LHS head *)
                 change [-9; -8; -5] with ([-9] ++ -8 :: [-5]).
                 apply Permutation_trans with (l' := -8 :: ([-9] ++ [-5])).
                 --- apply perm_skip.
                     (* Goal: Permutation [-5; -9] [-9; -5] *)
                     apply perm_swap.
                 --- apply Permutation_middle.
              ** apply Permutation_middle.
           ++ apply Permutation_middle.
        -- apply Permutation_middle.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.