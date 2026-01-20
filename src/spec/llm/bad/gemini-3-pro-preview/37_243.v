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
  [-5; -7; 2; 10; 11; 0; 9; 5; 2; 8; 11; 7] 
  [-5; -7; 2; 10; 2; 0; 9; 5; 11; 8; 11; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [
        simpl in Hodd;
        try discriminate Hodd;
        simpl;
        try reflexivity;
        simpl in Hlen; lia
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        (* Goal: Permutation [-5; 2; 11; 9; 2; 11] [-5; 2; 2; 9; 11; 11] *)
        apply perm_skip. (* -5 *)
        apply perm_skip. (* 2 *)
        (* Goal: Permutation [11; 9; 2; 11] [2; 9; 11; 11] *)
        apply perm_trans with (l' := 11 :: 2 :: 9 :: 11).
        { apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := 2 :: 11 :: 9 :: 11).
        { apply perm_swap. }
        apply perm_skip. (* 2 *)
        (* Goal: Permutation [11; 9; 11] [9; 11; 11] *)
        apply perm_swap.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.