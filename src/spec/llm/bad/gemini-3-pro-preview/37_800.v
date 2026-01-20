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
  [5; 3; -5; 2; -2; 3; -9; 2; 0; 123; 1; 9; -10; 12] 
  [-10; 3; -9; 2; -5; 3; -2; 2; 0; 123; 1; 9; 5; 12].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* 5 *)
        transitivity ([-10; -9; -5; -2; 0; 1] ++ [5]). 2: reflexivity.
        apply Permutation_trans with (l' := 5 :: [-10; -9; -5; -2; 0; 1] ++ []). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* -5 *)
        transitivity ([-10; -9] ++ -5 :: [-2; 0; 1]). 2: reflexivity.
        apply Permutation_trans with (l' := -5 :: [-10; -9] ++ [-2; 0; 1]). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* -2 *)
        transitivity ([-10; -9] ++ -2 :: [0; 1]). 2: reflexivity.
        apply Permutation_trans with (l' := -2 :: [-10; -9] ++ [0; 1]). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* -9 *)
        transitivity ([-10] ++ -9 :: [0; 1]). 2: reflexivity.
        apply Permutation_trans with (l' := -9 :: [-10] ++ [0; 1]). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* 0 *)
        transitivity ([-10] ++ 0 :: [1]). 2: reflexivity.
        apply Permutation_trans with (l' := 0 :: [-10] ++ [1]). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* 1 *)
        transitivity ([-10] ++ 1 :: []). 2: reflexivity.
        apply Permutation_trans with (l' := 1 :: [-10] ++ []). 2: apply Permutation_middle.
        apply Permutation_cons. simpl.
        (* -10 *)
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil); try lia.
Qed.