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

Example test_sort_even_case : sort_even_spec [4; 1; 3; 4; 5; 6; 3; 7; 8; 9; -1; 11; 12; 12] [-1; 1; 3; 4; 3; 6; 4; 7; 5; 9; 8; 11; 12; 12].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i as [|i]; [ try (simpl in Hodd; discriminate); try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (4 :: [-1; 3; 3] ++ [5; 8; 12]). { apply Permutation_middle. } apply Permutation_cons.
        apply Permutation_trans with (3 :: [-1] ++ [3; 5; 8; 12]). { apply Permutation_middle. } apply Permutation_cons.
        apply Permutation_trans with (5 :: [-1; 3] ++ [8; 12]). { apply Permutation_middle. } apply Permutation_cons.
        apply Permutation_trans with (3 :: [-1] ++ [8; 12]). { apply Permutation_middle. } apply Permutation_cons.
        apply Permutation_trans with (8 :: [-1] ++ [12]). { apply Permutation_middle. } apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try lia; try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.