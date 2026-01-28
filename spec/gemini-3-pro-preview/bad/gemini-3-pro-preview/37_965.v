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
  [5; 3; 2; 5; -3; 3; -11; 0; 123; 0; -10; 3; 3; 3; -9; 3] 
  [-11; 3; -10; 5; -9; 3; -3; 0; 2; 0; 3; 3; 5; 3; 123; 3].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 16 (destruct i as [|i]; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (-11 :: [5; 2; -3] ++ [123; -10; 3; -9]).
        { change [5; 2; -3; -11; 123; -10; 3; -9] with ([5; 2; -3] ++ -11 :: [123; -10; 3; -9]).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (-10 :: [5; 2; -3; 123] ++ [3; -9]).
        { change [5; 2; -3; 123; -10; 3; -9] with ([5; 2; -3; 123] ++ -10 :: [3; -9]).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (-9 :: [5; 2; -3; 123; 3] ++ []).
        { change [5; 2; -3; 123; 3; -9] with ([5; 2; -3; 123; 3] ++ -9 :: []).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (-3 :: [5; 2] ++ [123; 3]).
        { change [5; 2; -3; 123; 3] with ([5; 2] ++ -3 :: [123; 3]).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (2 :: [5] ++ [123; 3]).
        { change [5; 2; 123; 3] with ([5] ++ 2 :: [123; 3]).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (3 :: [5; 123] ++ []).
        { change [5; 123; 3] with ([5; 123] ++ 3 :: []).
          symmetry. apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.