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

Example test_sort_even_case : sort_even_spec [1; 3; 4; 5; 6; 3; 7; 8; 14; 9; -1; 11; 12] [-1; 3; 1; 5; 4; 3; 6; 8; 7; 9; 12; 11; 14].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (try (simpl in Hlen; lia); destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
    + split.
      * simpl.
        apply Permutation_trans with (l' := -1 :: [1; 4; 6; 7; 14] ++ [12]).
        { apply Permutation_sym. apply Permutation_middle with (l1 := [1; 4; 6; 7; 14]). }
        { simpl. apply perm_skip. do 4 apply perm_skip. apply perm_swap. }
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.