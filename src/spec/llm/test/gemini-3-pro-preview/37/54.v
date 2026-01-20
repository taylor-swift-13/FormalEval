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

Example test_sort_even_case : sort_even_spec [3; 2; 5; 2; 2; 1; 1; 3; 1] [1; 2; 1; 2; 2; 1; 3; 3; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      simpl in Hlen. lia.
    + split.
      * simpl.
        transitivity (1 :: [3; 5; 2] ++ [1]).
        { change [3; 5; 2; 1; 1] with ([3; 5; 2] ++ 1 :: [1]). apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        transitivity (1 :: [3; 5; 2] ++ []).
        { change [3; 5; 2; 1] with ([3; 5; 2] ++ 1 :: []). apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        transitivity (2 :: [3; 5] ++ []).
        { change [3; 5; 2] with ([3; 5] ++ 2 :: []). apply Permutation_sym, Permutation_middle. }
        apply perm_skip. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| constructor; try lia]).
        apply Sorted_nil.
Qed.