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
  [5; 10; -6; 2; -3; 3; -9; 0; 1; -10; 10; 2] 
  [-9; 10; -6; 2; -3; 3; 1; 0; 5; -10; 10; 2].
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
        assert (H1: Permutation [5; -6; -3; -9; 1; 10] (-9 :: [5; -6; -3; 1; 10])).
        { change [5; -6; -3; -9; 1; 10] with ([5; -6; -3] ++ -9 :: [1; 10]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H1. apply Permutation_cons.
        assert (H2: Permutation [5; -6; -3; 1; 10] (-6 :: [5; -3; 1; 10])).
        { change [5; -6; -3; 1; 10] with ([5] ++ -6 :: [-3; 1; 10]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H2. apply Permutation_cons.
        assert (H3: Permutation [5; -3; 1; 10] (-3 :: [5; 1; 10])).
        { change [5; -3; 1; 10] with ([5] ++ -3 :: [1; 10]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H3. apply Permutation_cons.
        assert (H4: Permutation [5; 1; 10] (1 :: [5; 10])).
        { change [5; 1; 10] with ([5] ++ 1 :: [10]).
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H4. apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.