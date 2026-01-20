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
  [5; -2; -12; 4; 23; 2; 3; 11; 12; -10; 5; 2] 
  [-12; -2; 3; 4; 5; 2; 5; 11; 12; -10; 23; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 23; 3; 12; 5] [-12; 3; 5; 5; 12; 23] *)
        transitivity (-12 :: [5; 23; 3; 12; 5]).
        { symmetry. change [5; -12; 23; 3; 12; 5] with ([5] ++ -12 :: [23; 3; 12; 5]). apply Permutation_middle. }
        apply Permutation_cons.
        transitivity (3 :: [5; 23; 12; 5]).
        { symmetry. change [5; 23; 3; 12; 5] with ([5; 23] ++ 3 :: [12; 5]). apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_cons.
        transitivity (5 :: [23; 12]).
        { symmetry. change [23; 12; 5] with ([23; 12] ++ 5 :: []). apply Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_swap.
      * (* 4. Sorted check *)
        simpl.
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