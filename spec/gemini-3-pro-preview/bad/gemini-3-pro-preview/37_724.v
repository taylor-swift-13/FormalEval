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
  [5; 0; 5; 5; 0; 6; 5; -1; 4; 5; 5; 0; 5] 
  [0; 0; 4; 5; 5; 6; 5; -1; 5; 5; 5; 0; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        assert (H1: Permutation [5; 5; 0; 5; 4; 5; 5] (0 :: [5; 5; 5; 4; 5; 5])).
        { replace [5; 5; 0; 5; 4; 5; 5] with ([5; 5] ++ 0 :: [5; 4; 5; 5]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H1. clear H1.
        apply Permutation_cons.
        assert (H2: Permutation [5; 5; 5; 4; 5; 5] (4 :: [5; 5; 5; 5; 5])).
        { replace [5; 5; 5; 4; 5; 5] with ([5; 5; 5] ++ 4 :: [5; 5]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H2. clear H2.
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.