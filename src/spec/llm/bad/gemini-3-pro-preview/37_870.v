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
  [5; 3; -5; -3; 3; -2; -9; 0; 6; -6; -2; -10; -5] 
  [-9; 3; -5; -3; -5; -2; -2; 0; 3; -6; 5; -10; 6].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [-9] ++ [5; -5; 3] ++ [6; -2; -5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := [-5] ++ [5] ++ [3; 6; -2; -5]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := [-5] ++ [5; 3; 6; -2] ++ []).
        { rewrite app_nil_r. apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := [-2] ++ [5; 3; 6] ++ []).
        { rewrite app_nil_r. apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := [3] ++ [5] ++ [6]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons || apply HdRel_cons || apply Sorted_nil || apply HdRel_nil); try lia.
Qed.