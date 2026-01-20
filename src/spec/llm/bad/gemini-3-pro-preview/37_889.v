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

Example test_sort_even_case : sort_even_spec [5; 10; 2; 3; -9; 0; 1; -10; 10; 2] [-9; 10; 1; 3; 2; 0; 5; -10; 10; 2].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply (Permutation_cons_app _ [-9; 1; 2] [10]). simpl.
        apply (Permutation_cons_app _ [-9; 1] [10]). simpl.
        apply (Permutation_cons_app _ [] [1; 10]). simpl.
        apply (Permutation_cons_app _ [] [10]). simpl.
        apply (Permutation_cons_app _ [] []). simpl.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.