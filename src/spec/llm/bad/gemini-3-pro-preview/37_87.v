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

Example test_sort_even_case : sort_even_spec [3; 3; 2; 0; 2; 1; 11; 1; 4; 3; 2] [2; 3; 2; 0; 2; 1; 3; 1; 4; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We iterate through indices 0 to 10 *)
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 11, length constraint is violated *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: Permutation [3; 2; 2; 11; 4; 2] [2; 2; 2; 3; 4; 11] *)
        (* 1. Pull first 2 *)
        transitivity (2 :: [3; 2; 11; 4; 2]).
        { apply Permutation_sym. change [3; 2; 2; 11; 4; 2] with ([3] ++ 2 :: [2; 11; 4; 2]). apply Permutation_middle. }
        apply Permutation_cons.
        (* 2. Pull second 2 *)
        transitivity (2 :: [3; 11; 4; 2]).
        { apply Permutation_sym. change [3; 2; 11; 4; 2] with ([3] ++ 2 :: [11; 4; 2]). apply Permutation_middle. }
        apply Permutation_cons.
        (* 3. Pull third 2 *)
        transitivity (2 :: [3; 11; 4]).
        { apply Permutation_sym. change [3; 11; 4; 2] with ([3; 11; 4] ++ 2 :: []). apply Permutation_middle. }
        apply Permutation_cons.
        (* 4. Match 3 *)
        apply Permutation_cons.
        (* 5. Swap 11 and 4 *)
        apply Permutation_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.