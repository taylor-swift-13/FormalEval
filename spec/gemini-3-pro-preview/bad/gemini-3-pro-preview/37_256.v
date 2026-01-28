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
  [5; 3; -5; 2; -3; 3; -9; 0; 123; 1; -10; 2; -3] 
  [-10; 3; -9; 2; -5; 3; -3; 0; -3; 1; 5; 2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      simpl in Hodd.
      do 13 (destruct i; [ try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (5 :: [-10; -9; -5; -3; -3; 123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (-5 :: [-10; -9; -3; -3; 123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (-3 :: [-10; -9; -3; 123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (-9 :: [-10; -3; 123]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (123 :: [-10; -3]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        transitivity (-10 :: [-3]).
        2: apply Permutation_middle.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia || apply HdRel_nil]).
        apply Sorted_nil.
Qed.