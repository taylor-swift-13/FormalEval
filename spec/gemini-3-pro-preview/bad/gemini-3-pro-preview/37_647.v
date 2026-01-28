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
  [5; 3; 10; -5; 2; -3; 3; -9; 0; 123; 1; -10; 10; -5] 
  [0; 3; 1; -5; 2; -3; 3; -9; 5; 123; 10; -10; 10; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (0 :: [5; 10; 2; 3] ++ [1; 10]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        apply Permutation_trans with (1 :: [5; 10; 2; 3] ++ [10]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        apply Permutation_trans with (2 :: [5; 10] ++ [3; 10]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        apply Permutation_trans with (3 :: [5; 10] ++ [10]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| first [apply HdRel_nil | apply HdRel_cons; lia] ]).
        apply Sorted_nil.
Qed.