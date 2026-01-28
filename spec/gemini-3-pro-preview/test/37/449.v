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

Example test_sort_even_case : sort_even_spec [3; -7; 2; 10; 11; 0; 9; 5; 2; 8; 11; 7] [2; -7; 2; 10; 3; 0; 9; 5; 11; 8; 11; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i as [|i]; simpl in *; [ try discriminate; try reflexivity | ]).
      lia.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1 := [2; 2]) (l2 := [9; 11; 11]).
        simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [2; 9; 11; 11]).
        simpl.
        apply Permutation_cons_app with (l1 := [2; 9]) (l2 := [11]).
        simpl.
        apply Permutation_cons_app with (l1 := [2]) (l2 := [11]).
        simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.