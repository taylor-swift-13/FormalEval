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

Example test_sort_even_case : sort_even_spec [3; 0; 0; 4; 1; 5; 9; 2; 6; 5; 3; 3] [0; 0; 1; 4; 3; 5; 3; 2; 6; 5; 9; 3].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [0; 3; 1; 9; 6; 3]).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_trans with (l' := [1; 3; 9; 6; 3]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_skip.
        apply Permutation_trans with (l' := [3; 9; 6]).
        { apply Permutation_trans with (l' := [9; 3; 6]).
          - apply perm_skip. apply perm_swap.
          - apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil || lia).
Qed.