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

Example test_sort_even_case : sort_even_spec [5; 3; 6; -5; 2; -3; 3; 0; 123; 1; -10; 5] [-10; 3; 2; -5; 3; -3; 5; 0; 6; 1; 123; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := -10 :: [5; 6; 2; 3; 123]).
        { change [5; 6; 2; 3; 123; -10] with ([5; 6; 2; 3; 123] ++ -10 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := 2 :: [5; 6; 3; 123]).
        { change [5; 6; 2; 3; 123] with ([5; 6] ++ 2 :: [3; 123]).
          apply Permutation_sym, Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (l' := 3 :: [5; 6; 123]).
        { change [5; 6; 3; 123] with ([5; 6] ++ 3 :: [123]).
          apply Permutation_sym, Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; simpl; try lia ]).
        apply Sorted_nil.
Qed.