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

Example test_sort_even_case : sort_even_spec [5; 3; 6; -5; 2; -3; 3; -9; 0; 123; 1; -10] [0; 3; 1; -5; 2; -3; 3; -9; 5; 123; 6; -10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        assert (Permutation [5; 6; 2; 3; 0; 1] (0 :: [5; 6; 2; 3; 1])).
        { change [5; 6; 2; 3; 0; 1] with ([5; 6; 2; 3] ++ 0 :: [1]).
          apply Permutation_sym, Permutation_middle. }
        apply (Permutation_trans H); clear H; apply Permutation_cons.

        assert (Permutation [5; 6; 2; 3; 1] (1 :: [5; 6; 2; 3])).
        { change [5; 6; 2; 3; 1] with ([5; 6; 2; 3] ++ 1 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply (Permutation_trans H); clear H; apply Permutation_cons.

        assert (Permutation [5; 6; 2; 3] (2 :: [5; 6; 3])).
        { change [5; 6; 2; 3] with ([5; 6] ++ 2 :: [3]).
          apply Permutation_sym, Permutation_middle. }
        apply (Permutation_trans H); clear H; apply Permutation_cons.

        assert (Permutation [5; 6; 3] (3 :: [5; 6])).
        { change [5; 6; 3] with ([5; 6] ++ 3 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply (Permutation_trans H); clear H; apply Permutation_cons.

        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.