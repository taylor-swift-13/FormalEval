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
  [4; -2; -12; -9; 23; 2; 3; 11; 13; -10; 4; -13; -12; 4] 
  [-12; -2; -12; -9; 3; 2; 4; 11; 4; -10; 13; -13; 23; 4].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate Hodd; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 4 :: [-12; -12; 3] ++ [4; 13; 23]).
        { apply Permutation_middle with (l1 := [-12; -12; 3]). }
        apply Permutation_cons.
        
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := 23 :: [-12; 3; 4; 13] ++ []).
        { apply Permutation_middle with (l1 := [-12; 3; 4; 13]). }
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := 3 :: [-12] ++ [4; 13]).
        { apply Permutation_middle with (l1 := [-12]). }
        apply Permutation_cons.
        
        apply Permutation_trans with (l' := 13 :: [-12; 4] ++ []).
        { apply Permutation_middle with (l1 := [-12; 4]). }
        apply Permutation_cons.
        
        apply Permutation_swap.
      * simpl.
        repeat (constructor; try lia).
Qed.