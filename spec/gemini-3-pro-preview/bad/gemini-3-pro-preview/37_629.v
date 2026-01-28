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

Example test_sort_even_case : sort_even_spec [5; -2; -12; 4; 23; 2; 3; 11; 12; -9] [-12; -2; 3; 4; 5; 2; 12; 11; 23; -9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [-12; 3; 5; 12; 23] with ([-12; 3] ++ 5 :: [12; 23]).
        apply Permutation_trans with (5 :: [-12; 3] ++ [12; 23]).
        apply Permutation_cons.
        simpl.
        apply Permutation_cons.
        change [3; 12; 23] with ([3; 12] ++ 23 :: []).
        apply Permutation_trans with (23 :: [3; 12] ++ []).
        apply Permutation_cons.
        simpl.
        apply Permutation_refl.
        apply Permutation_middle.
        apply Permutation_middle.
      * simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia]).
        apply Sorted_cons.
        apply Sorted_nil.
        apply HdRel_nil.
Qed.