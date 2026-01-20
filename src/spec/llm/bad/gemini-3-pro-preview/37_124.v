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
  [5; -2; -12; 4; 4; 23; 2; 3; 11; 12; -10]
  [-12; -2; -10; 4; 2; 23; 4; 3; 5; 12; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (match goal with
              | [ n : nat |- context [nth n _ _] ] =>
                destruct n; [ simpl in *; try discriminate; try reflexivity | ]
              end).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: Permutation [5; -12; 4; 2; 11; -10] [-12; -10; 2; 4; 5; 11] *)
        (* Move -12 to front *)
        apply Permutation_trans with (l' := -12 :: 5 :: 4 :: 2 :: 11 :: -10 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons.
        (* Move -10 to front *)
        apply Permutation_trans with (l' := -10 :: 5 :: 4 :: 2 :: 11 :: nil).
        { change (5 :: 4 :: 2 :: 11 :: -10 :: nil) with ([5; 4; 2; 11] ++ [-10]).
          apply Permutation_trans with (l' := [-10] ++ [5; 4; 2; 11]).
          apply Permutation_app_comm.
          simpl. apply Permutation_refl. }
        apply Permutation_cons.
        (* Move 2 to front *)
        apply Permutation_trans with (l' := 5 :: 2 :: 4 :: 11 :: nil).
        { apply Permutation_cons. apply Permutation_swap. }
        apply Permutation_trans with (l' := 2 :: 5 :: 4 :: 11 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons.
        (* Move 4 to front *)
        apply Permutation_trans with (l' := 4 :: 5 :: 11 :: nil).
        { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.