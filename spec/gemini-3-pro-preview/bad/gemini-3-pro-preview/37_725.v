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
  [5; 10; -6; 2; -3; 3; 0; -9; 0; 1; -10; 10; 2] 
  [-10; 10; -6; 2; -3; 3; 0; -9; 0; 1; 2; 10; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := [-6; -3; 0; 0; -10; 2] ++ [5]).
        { apply Permutation_app_comm. }
        apply Permutation_app_tail.
        apply Permutation_trans with (l' := ([-10] ++ [-6; -3; 0; 0]) ++ [2]).
        { apply Permutation_app_tail.
          change ([-6; -3; 0; 0; -10]) with ([-6; -3; 0; 0] ++ [-10]).
          apply Permutation_app_comm. }
        simpl. apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.