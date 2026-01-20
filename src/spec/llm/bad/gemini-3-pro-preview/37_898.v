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

Example test_sort_even_case : sort_even_spec [3; -5; 23; -3; 3; -9; 0; 123; 1; -10; 1] [0; -5; 1; -3; 1; -9; 3; 123; 3; -10; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { reflexivity. } (* 1 *)
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { reflexivity. } (* 3 *)
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { reflexivity. } (* 5 *)
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { reflexivity. } (* 7 *)
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { reflexivity. } (* 9 *)
      destruct i. { simpl in Hodd. discriminate. }
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply perm_trans with (0 :: [3; 23; 3] ++ [1; 1]).
        { change [3; 23; 3; 0; 1; 1] with ([3; 23; 3] ++ 0 :: [1; 1]).
          apply Permutation_sym, Permutation_middle. }
        simpl. apply perm_skip.
        
        apply perm_trans with (1 :: [3; 23; 3] ++ [1]).
        { change [3; 23; 3; 1; 1] with ([3; 23; 3] ++ 1 :: [1]).
          apply Permutation_sym, Permutation_middle. }
        simpl. apply perm_skip.

        apply perm_trans with (1 :: [3; 23; 3] ++ []).
        { change [3; 23; 3; 1] with ([3; 23; 3] ++ 1 :: []).
          apply Permutation_sym, Permutation_middle. }
        simpl. apply perm_skip.

        apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- repeat (apply HdRel_cons; try lia).
Qed.