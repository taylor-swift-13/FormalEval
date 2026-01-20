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

Example test_sort_even_case : sort_even_spec [1; 2; 3; 2; 12; 6; -8; 8; 2] [-8; 2; 1; 2; 2; 6; 3; 8; 12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 9 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 3; 12; -8; 2] [-8; 1; 2; 3; 12] *)
        (* Move -8 to front *)
        apply Permutation_trans with (l' := 1 :: 3 :: -8 :: 12 :: 2 :: []).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 1 :: -8 :: 3 :: 12 :: 2 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := -8 :: 1 :: 3 :: 12 :: 2 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [1; 3; 12; 2] [1; 2; 3; 12] *)
        apply perm_skip.
        (* Goal: Permutation [3; 12; 2] [2; 3; 12] *)
        (* Move 2 to front of remaining list *)
        apply Permutation_trans with (l' := 3 :: 2 :: 12 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 2 :: 3 :: 12 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [3; 12] [3; 12] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.