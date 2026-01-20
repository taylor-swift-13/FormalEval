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

Example test_sort_even_case : sort_even_spec [3; 1; 4; -6; 1; 5; 9; 10; 6; 4; 4] [1; 1; 3; -6; 4; 5; 4; 10; 6; 4; 9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        assert (H1: Permutation [3; 4; 1; 9; 6; 4] (1 :: [3; 4] ++ [9; 6; 4])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H1. rewrite H1. apply perm_skip.
        apply perm_skip.
        apply perm_skip.
        assert (H2: Permutation [9; 6; 4] (4 :: [9; 6] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        simpl in H2. rewrite H2. apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| try apply HdRel_cons; try apply HdRel_nil; try lia]).
        apply Sorted_nil.
Qed.