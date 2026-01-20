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

Example test_sort_even_case : sort_even_spec [3; -5; 12; -3; 3; -9; 0; 123; -10] [-10; -5; 0; -3; 3; -9; 3; 123; 12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 9 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [3; 12; 3; 0; -10] [-10; 0; 3; 3; 12] *)
        
        change [-10; 0; 3; 3; 12] with ([-10; 0] ++ 3 :: [3; 12]).
        apply Permutation_trans with (l' := 3 :: ([-10; 0] ++ [3; 12])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        change [-10; 0; 3; 12] with ([-10; 0; 3] ++ 12 :: []).
        apply Permutation_trans with (l' := 12 :: ([-10; 0; 3] ++ [])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        change [-10; 0; 3] with ([-10; 0] ++ 3 :: []).
        apply Permutation_trans with (l' := 3 :: ([-10; 0] ++ [])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        change [-10; 0] with ([-10] ++ 0 :: []).
        apply Permutation_trans with (l' := 0 :: ([-10] ++ [])); [ | apply Permutation_middle ].
        apply Permutation_cons.
        
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.