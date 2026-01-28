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

Example test_sort_even_case : sort_even_spec [5; -2; -12; 4; 23; 2; 3; 11; 12; -10; 3] [-12; -2; 3; 4; 3; 2; 5; 11; 12; -10; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Perform case analysis on i up to the length of the list (11) *)
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 11, length condition is violated *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 23; 3; 12; 3] [-12; 3; 3; 5; 12; 23] *)
        
        (* Move 5 to the correct position *)
        change [-12; 3; 3; 5; 12; 23] with ([-12; 3; 3] ++ 5 :: [12; 23]).
        apply Permutation_trans with (l' := 5 :: ([-12; 3; 3] ++ [12; 23])).
        2: apply Permutation_middle.
        apply perm_skip. simpl.
        
        (* -12 is already at head *)
        apply perm_skip.
        
        (* Move 23 to the correct position *)
        change [3; 3; 12; 23] with ([3; 3; 12] ++ 23 :: []).
        apply Permutation_trans with (l' := 23 :: ([3; 3; 12] ++ [])).
        2: apply Permutation_middle.
        apply perm_skip. simpl.
        
        (* 3 is already at head *)
        apply perm_skip.
        
        (* Move 12 to the correct position *)
        change [3; 12] with ([3] ++ 12 :: []).
        apply Permutation_trans with (l' := 12 :: ([3] ++ [])).
        2: apply Permutation_middle.
        apply perm_skip. simpl.
        
        (* Remaining list [3] matches *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.