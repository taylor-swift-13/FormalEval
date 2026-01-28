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
  [-5; -7; 123; 2; -3; 0; 9; 5; -3; 2; 8; 3; 7; 2; 8] 
  [-5; -7; -3; 2; -3; 0; 7; 5; 8; 2; 8; 3; 9; 2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        apply Permutation_cons_app with (l1 := [-3; -3; 7; 8; 8; 9]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [-3; 7; 8; 8; 9]). simpl.
        apply Permutation_cons_app with (l1 := [-3; 7; 8; 8]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [7; 8; 8]). simpl.
        apply Permutation_cons_app with (l1 := [7]) (l2 := [8]). simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [8]). simpl.
        apply Permutation_refl.
      * simpl.
        repeat constructor; try lia.
Qed.