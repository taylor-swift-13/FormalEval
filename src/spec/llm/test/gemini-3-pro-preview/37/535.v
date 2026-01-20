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

Example test_sort_even_case : sort_even_spec [-5; 8; -5; 2; 9; 5; -3; 2; 8; 7; 3; 7; 2] [-5; 8; -5; 2; -3; 5; 2; 2; 3; 7; 8; 7; 9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      assert (Hcases: i = 1%nat \/ i = 3%nat \/ i = 5%nat \/ i = 7%nat \/ i = 9%nat \/ i = 11%nat).
      {
        destruct i. simpl in Hodd. discriminate.
        destruct i. left. reflexivity. (* 1 *)
        destruct i. simpl in Hodd. discriminate.
        destruct i. right. left. reflexivity. (* 3 *)
        destruct i. simpl in Hodd. discriminate.
        destruct i. right. right. left. reflexivity. (* 5 *)
        destruct i. simpl in Hodd. discriminate.
        destruct i. right. right. right. left. reflexivity. (* 7 *)
        destruct i. simpl in Hodd. discriminate.
        destruct i. right. right. right. right. left. reflexivity. (* 9 *)
        destruct i. simpl in Hodd. discriminate.
        destruct i. right. right. right. right. right. reflexivity. (* 11 *)
        destruct i. simpl in Hodd. discriminate.
        simpl in Hlen. lia.
      }
      destruct Hcases as [-> | [-> | [-> | [-> | [-> | ->]]]]]; simpl; reflexivity.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply perm_skip. (* -5 *)
        apply perm_skip. (* -5 *)
        (* Goal: Permutation [9; -3; 8; 3; 2] [-3; 2; 3; 8; 9] *)
        apply Permutation_trans with (l' := -3 :: [9; 8; 3; 2]).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [9; 8; 3; 2] [2; 3; 8; 9] *)
        apply Permutation_trans with (l' := 2 :: [9; 8; 3]).
        { apply Permutation_sym. apply Permutation_cons_append. }
        apply perm_skip.
        (* Goal: Permutation [9; 8; 3] [3; 8; 9] *)
        apply Permutation_trans with (l' := 3 :: [9; 8]).
        { apply Permutation_sym. apply Permutation_cons_append. }
        apply perm_skip.
        (* Goal: Permutation [9; 8] [8; 9] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil); try lia.
Qed.