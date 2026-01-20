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
  [3; 3; 2; 2; 1; 11; 1; 3; 2; 0] 
  [1; 3; 1; 2; 2; 11; 2; 3; 3; 0].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 10 (destruct i; [ 
        simpl in Hodd; try discriminate; simpl; try reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [3; 2; 1; 1; 2] [1; 1; 2; 2; 3] *)
        (* Move 1 (index 2) to front *)
        apply Permutation_trans with (l' := [3; 1; 2; 1; 2]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [1; 3; 2; 1; 2]).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [3; 2; 1; 2] [1; 2; 2; 3] *)
        (* Move 1 (index 2) to front *)
        apply Permutation_trans with (l' := [3; 1; 2; 2]).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := [1; 3; 2; 2]).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [3; 2; 2] [2; 2; 3] *)
        (* Move 2 (index 1) to front *)
        apply Permutation_trans with (l' := [2; 3; 2]).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [3; 2] [2; 3] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.