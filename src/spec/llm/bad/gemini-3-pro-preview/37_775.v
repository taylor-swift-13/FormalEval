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

Example test_sort_even_case : sort_even_spec [5; 0; 5; 5; 0; 5; 0; 5; 0; -2; 5; -3; 0] [0; 0; 0; 5; 0; 5; 0; 5; 5; -2; 5; -3; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; 5; 0; 0; 0; 5; 0] [0; 0; 0; 0; 5; 5; 5] *)
        (* Sort by moving 0s to the front one by one using Permutation_middle *)
        
        (* 1st 0 (index 2 in LHS) *)
        apply Permutation_trans with (0 :: [5; 5; 0; 0; 5; 0]).
        { apply Permutation_sym.
          change [5; 5; 0; 0; 0; 5; 0] with ([5; 5] ++ 0 :: [0; 0; 5; 0]).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* 2nd 0 (index 2 in remaining) *)
        apply Permutation_trans with (0 :: [5; 5; 0; 5; 0]).
        { apply Permutation_sym.
          change [5; 5; 0; 0; 5; 0] with ([5; 5] ++ 0 :: [0; 5; 0]).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* 3rd 0 (index 2 in remaining) *)
        apply Permutation_trans with (0 :: [5; 5; 5; 0]).
        { apply Permutation_sym.
          change [5; 5; 0; 5; 0] with ([5; 5] ++ 0 :: [5; 0]).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* 4th 0 (index 3 in remaining) *)
        apply Permutation_trans with (0 :: [5; 5; 5]).
        { apply Permutation_sym.
          change [5; 5; 5; 0] with ([5; 5; 5] ++ 0 :: []).
          apply Permutation_middle. }
        apply Permutation_cons.

        (* Remaining list is [5; 5; 5], which matches *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.