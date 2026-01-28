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
  [5; 0; 5; 5; 0; 5; 4; 0; 0; 5; 0; 5; 4] 
  [0; 0; 0; 5; 0; 5; 4; 0; 4; 5; 5; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* Permutation proof by moving elements to the front *)
        change [5; 5; 0; 4; 0; 0; 4] with ([5; 5] ++ 0 :: [4; 0; 0; 4]).
        apply Permutation_trans with (0 :: [5; 5] ++ [4; 0; 0; 4]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_skip. simpl.

        change [5; 5; 4; 0; 0; 4] with ([5; 5; 4] ++ 0 :: [0; 4]).
        apply Permutation_trans with (0 :: [5; 5; 4] ++ [0; 4]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_skip. simpl.

        change [5; 5; 4; 0; 4] with ([5; 5; 4] ++ 0 :: [4]).
        apply Permutation_trans with (0 :: [5; 5; 4] ++ [4]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_skip. simpl.

        change [5; 5; 4; 4] with ([5; 5] ++ 4 :: [4]).
        apply Permutation_trans with (4 :: [5; 5] ++ [4]).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_skip. simpl.

        change [5; 5; 4] with ([5; 5] ++ 4 :: []).
        apply Permutation_trans with (4 :: [5; 5] ++ []).
        { apply Permutation_sym, Permutation_middle. }
        apply Permutation_skip. simpl.

        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; lia ]).
        apply Sorted_nil.
Qed.