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

Example test_sort_even_case : sort_even_spec [5; 0; 5; 5; 0; 5; 0; 5; 5; 0] [0; 0; 0; 5; 5; 5; 5; 5; 5; 0].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | simpl in Hlen; try lia ]).
    + split.
      * simpl.
        (* Goal: Permutation [5; 5; 0; 0; 5] [0; 0; 5; 5; 5] *)
        (* Move first 0 (index 2) to front *)
        apply Permutation_trans with (l' := 5 :: 0 :: 5 :: 0 :: 5 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 0 :: 5 :: 5 :: 0 :: 5 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [5; 5; 0; 5] [0; 5; 5; 5] *)
        (* Move remaining 0 (index 2) to front *)
        apply Permutation_trans with (l' := 5 :: 0 :: 5 :: 5 :: []).
        { apply perm_skip. apply perm_swap. }
        apply Permutation_trans with (l' := 0 :: 5 :: 5 :: 5 :: []).
        { apply perm_swap. }
        apply perm_skip.
        (* Goal: Permutation [5; 5; 5] [5; 5; 5] *)
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.