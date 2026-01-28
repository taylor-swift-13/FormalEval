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
  [-5; -7; 2; 0; 9; 5; -3; 2; 8; 3; 7; 2; 2] 
  [-5; -7; -3; 0; 2; 5; 2; 2; 7; 3; 8; 2; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      destruct i. simpl. reflexivity.
      destruct i. simpl in Hodd; discriminate.
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons. reflexivity.
        etransitivity.
        2: apply Permutation_cons.
        change (2 :: 9 :: -3 :: 8 :: 7 :: 2 :: []) with ([2; 9] ++ -3 :: [8; 7; 2]).
        apply Permutation_sym. apply Permutation_middle.
        simpl.
        apply Permutation_cons. reflexivity.
        etransitivity.
        2: apply Permutation_cons.
        change (9 :: 8 :: 7 :: 2 :: []) with ([9; 8; 7] ++ 2 :: []).
        apply Permutation_sym. apply Permutation_middle.
        simpl.
        etransitivity.
        2: apply Permutation_cons.
        change (9 :: 8 :: 7 :: []) with ([9; 8] ++ 7 :: []).
        apply Permutation_sym. apply Permutation_middle.
        simpl. apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil).
        -- apply HdRel_nil.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
Qed.