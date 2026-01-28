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

Example test_sort_even_case : sort_even_spec [6; 5; 3; 6; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5] [1; 5; 1; 6; 3; 4; 3; 5; 6; 2; 6; 5; 9; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [1; 1; 3; 3]) (l2 := [6; 9]). simpl.
        apply Permutation_cons_app with (l1 := [1; 1]) (l2 := [3; 6; 9]). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [1; 3; 6; 9]). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [3; 6; 9]). simpl.
        apply Permutation_cons_app with (l1 := [3; 6]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [3]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := []). simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.