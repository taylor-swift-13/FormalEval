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
  [5; 3; -5; -3; 3; -2; -9; 0; 123; -2; 3] 
  [-9; 3; -5; -3; 3; -2; 3; 0; 5; -2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (5 :: [-9; -5; 3; 3; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [-9; -5; 3; 3] [123] 5). }
        apply Permutation_cons.
        transitivity (-5 :: [-9; 3; 3; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [-9] [3; 3; 123] (-5)). }
        apply Permutation_cons.
        transitivity (3 :: [-9; 3; 123]).
        { apply Permutation_sym. apply (Permutation_middle _ [-9] [3; 123] 3). }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; simpl; try lia ]).
        apply Sorted_nil.
Qed.