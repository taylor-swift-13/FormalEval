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
  [1; 2; 3; 2; 3; 6; 2; 7; 8; 2; 2; 1] 
  [1; 2; 2; 2; 2; 6; 3; 7; 3; 2; 8; 1].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate Hodd; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_cons.
        transitivity (2 :: [3; 3; 8; 2]).
        { change [3; 3; 2; 8; 2] with ([3; 3] ++ 2 :: [8; 2]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        transitivity (2 :: [3; 3; 8]).
        { change [3; 3; 8; 2] with ([3; 3; 8] ++ 2 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.