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

Example test_sort_even_case : sort_even_spec [11; -7; 2; 10; 2; 9; 5; -3; 2; 8; 3; 7; 10; -7] [2; -7; 2; 10; 2; 9; 3; -3; 5; 8; 10; 7; 11; -7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 14 (destruct i as [|i]; [
        try (simpl in Hodd; discriminate Hodd); (* Even indices *)
        try (simpl; reflexivity) (* Odd indices *)
        | idtac ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [11; 2; 2; 5; 2; 3; 10] Target: [2; 2; 2; 3; 5; 10; 11] *)
        apply Permutation_trans with (l' := 2 :: 11 :: 2 :: 5 :: 2 :: 3 :: 10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons. (* matched 2 *)
        (* Current: [11; 2; 5; 2; 3; 10] Target: [2; 2; 3; 5; 10; 11] *)
        apply Permutation_trans with (l' := 2 :: 11 :: 5 :: 2 :: 3 :: 10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons. (* matched 2 *)
        (* Current: [11; 5; 2; 3; 10] Target: [2; 3; 5; 10; 11] *)
        apply Permutation_trans with (l' := 11 :: 2 :: 5 :: 3 :: 10 :: nil).
        { apply Permutation_skip. apply Permutation_swap. }
        apply Permutation_trans with (l' := 2 :: 11 :: 5 :: 3 :: 10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons. (* matched 2 *)
        (* Current: [11; 5; 3; 10] Target: [3; 5; 10; 11] *)
        apply Permutation_trans with (l' := 11 :: 3 :: 5 :: 10 :: nil).
        { apply Permutation_skip. apply Permutation_swap. }
        apply Permutation_trans with (l' := 3 :: 11 :: 5 :: 10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons. (* matched 3 *)
        (* Current: [11; 5; 10] Target: [5; 10; 11] *)
        apply Permutation_trans with (l' := 5 :: 11 :: 10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons. (* matched 5 *)
        (* Current: [11; 10] Target: [10; 11] *)
        apply Permutation_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.