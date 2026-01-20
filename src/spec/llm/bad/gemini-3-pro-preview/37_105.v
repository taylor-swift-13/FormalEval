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
  [5; 3; -5; 2; -3; 3; -9; 0; 123; 1; -10] 
  [-10; 3; -9; 2; -5; 3; -3; 0; 5; 1; 123].
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
        apply Permutation_sym.
        change [5; -5; -3; -9; 123; -10] with ([5; -5; -3; -9; 123] ++ -10 :: []).
        apply Permutation_cons_app. simpl.
        change [5; -5; -3; -9; 123] with ([5; -5; -3] ++ -9 :: [123]).
        apply Permutation_cons_app. simpl.
        change [5; -5; -3; 123] with ([5] ++ -5 :: [-3; 123]).
        apply Permutation_cons_app. simpl.
        change [5; -3; 123] with ([5] ++ -3 :: [123]).
        apply Permutation_cons_app. simpl.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ constructor; try lia | ]).
        apply Sorted_nil.
Qed.