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
  [0; 3; -5; 2; -3; 3; -9; 0; 123; 1; -10; -5] 
  [-10; 3; -9; 2; -5; 3; -3; 0; 0; 1; 123; -5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 11 *)
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Handle indices >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [0; -5; -3; -9; 123; -10] [-10; -9; -5; -3; 0; 123] *)
        (* Move -10 to front using Permutation_app_comm *)
        change [0; -5; -3; -9; 123; -10] with ([0; -5; -3; -9; 123] ++ [-10]).
        apply Permutation_trans with ([-10] ++ [0; -5; -3; -9; 123]).
        { apply Permutation_app_comm. }
        simpl. apply perm_skip.
        (* Goal: Permutation [0; -5; -3; -9; 123] [-9; -5; -3; 0; 123] *)
        (* Move -9 to front *)
        apply Permutation_trans with (0 :: -5 :: -9 :: -3 :: 123 :: []).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (0 :: -9 :: -5 :: -3 :: 123 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (-9 :: 0 :: -5 :: -3 :: 123 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [0; -5; -3; 123] [-5; -3; 0; 123] *)
        (* Move -5 to front *)
        apply Permutation_trans with (-5 :: 0 :: -3 :: 123 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [0; -3; 123] [-3; 0; 123] *)
        (* Move -3 to front *)
        apply Permutation_trans with (-3 :: 0 :: 123 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [0; 123] [0; 123] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil); try lia.
Qed.