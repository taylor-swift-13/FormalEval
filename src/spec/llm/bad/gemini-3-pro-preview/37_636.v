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
  [5; 3; -5; -3; 3; -2; -9; 0; 123; -2; -10] 
  [-10; 3; -9; -3; -5; -2; 3; 0; 5; -2; 123].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        assert (H1: Permutation (5 :: [-10; -9; -5; 3; 123]) ([-10; -9; -5; 3] ++ 5 :: [123])) by apply Permutation_middle.
        simpl in H1. transitivity (5 :: [-10; -9; -5; 3; 123]); [ | exact H1 ].
        apply perm_skip.
        assert (H2: Permutation (-5 :: [-10; -9; 3; 123]) ([-10; -9] ++ -5 :: [3; 123])) by apply Permutation_middle.
        simpl in H2. transitivity (-5 :: [-10; -9; 3; 123]); [ | exact H2 ].
        apply perm_skip.
        assert (H3: Permutation (3 :: [-10; -9; 123]) ([-10; -9] ++ 3 :: [123])) by apply Permutation_middle.
        simpl in H3. transitivity (3 :: [-10; -9; 123]); [ | exact H3 ].
        apply perm_skip.
        assert (H4: Permutation (-9 :: [-10; 123]) ([-10] ++ -9 :: [123])) by apply Permutation_middle.
        simpl in H4. transitivity (-9 :: [-10; 123]); [ | exact H4 ].
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.