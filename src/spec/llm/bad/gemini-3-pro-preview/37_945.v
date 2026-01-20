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

Example test_sort_even_case : sort_even_spec [10; -6; 2; 3; -9; 0; 1; -10; 10; 2; 2] [-9; -6; 1; 3; 2; 0; 2; -10; 10; 2; 10].
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
        assert (H1: Permutation [10; 2; -9; 1; 10; 2] (-9 :: [10; 2; 1; 10; 2])).
        { apply Permutation_sym. change [10; 2; -9; 1; 10; 2] with ([10; 2] ++ -9 :: [1; 10; 2]). apply Permutation_middle. }
        transitivity (-9 :: [10; 2; 1; 10; 2]); [ assumption | ].
        apply Permutation_cons.
        
        assert (H2: Permutation [10; 2; 1; 10; 2] (1 :: [10; 2; 10; 2])).
        { apply Permutation_sym. change [10; 2; 1; 10; 2] with ([10; 2] ++ 1 :: [10; 2]). apply Permutation_middle. }
        transitivity (1 :: [10; 2; 10; 2]); [ assumption | ].
        apply Permutation_cons.
        
        assert (H3: Permutation [10; 2; 10; 2] (2 :: [10; 10; 2])).
        { apply Permutation_sym. change [10; 2; 10; 2] with ([10] ++ 2 :: [10; 2]). apply Permutation_middle. }
        transitivity (2 :: [10; 10; 2]); [ assumption | ].
        apply Permutation_cons.
        
        assert (H4: Permutation [10; 10; 2] (2 :: [10; 10])).
        { apply Permutation_sym. change [10; 10; 2] with ([10; 10] ++ 2 :: []). apply Permutation_middle. }
        transitivity (2 :: [10; 10]); [ assumption | ].
        apply Permutation_cons.
        
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_cons.
                  { apply Sorted_nil. }
                  { apply HdRel_nil. } }
                { apply HdRel_cons. lia. } }
              { apply HdRel_cons. lia. } }
            { apply HdRel_cons. lia. } }
          { apply HdRel_cons. lia. } }
        { apply HdRel_cons. lia. }
Qed.