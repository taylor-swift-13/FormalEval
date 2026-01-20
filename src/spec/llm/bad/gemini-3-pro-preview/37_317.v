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
  [5; 3; 7; 0; 2; -3; -10; 0; 123; 1; 0; -10; 123; 5] 
  [-10; 3; 0; 0; 2; -3; 5; 0; 7; 1; 123; -10; 123; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (-10 :: [5; 7; 2; 123; 0; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [5; 7; 2] [123; 0; 123] (-10)). }
        apply Permutation_cons.
        transitivity (0 :: [5; 7; 2; 123; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [5; 7; 2; 123] [123] 0). }
        apply Permutation_cons.
        transitivity (2 :: [5; 7; 123; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [5; 7] [123; 123] 2). }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (constructor; try lia).
Qed.