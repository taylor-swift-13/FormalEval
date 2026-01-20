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

Example test_sort_even_case : sort_even_spec [1; -4; 6; 5; 7; 2; 2; 8; 6] [1; -4; 2; 5; 6; 2; 6; 8; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate Hodd; try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 6; 7; 2; 6] [1; 2; 6; 6; 7] *)
        constructor. (* 1 matches *)
        (* Goal: Permutation [6; 7; 2; 6] [2; 6; 6; 7] *)
        apply Permutation_trans with (l' := 6 :: 2 :: 7 :: 6).
        { constructor. apply perm_swap. }
        apply Permutation_trans with (l' := 2 :: 6 :: 7 :: 6).
        { apply perm_swap. }
        constructor. (* 2 matches *)
        (* Goal: Permutation [6; 7; 6] [6; 6; 7] *)
        constructor. (* 6 matches *)
        (* Goal: Permutation [7; 6] [6; 7] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.