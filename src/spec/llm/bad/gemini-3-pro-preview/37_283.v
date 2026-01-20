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
  [-5; -7; 2; 10; 0; 5; -3; 2; 8; 3; 7; 0] 
  [-5; -7; -3; 10; 0; 5; 2; 2; 7; 3; 8; 0].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [-5; 2; 0; -3; 8; 7] [-5; -3; 0; 2; 7; 8] *)
        apply perm_skip.
        (* Goal: Permutation [2; 0; -3; 8; 7] [-3; 0; 2; 7; 8] *)
        apply Permutation_trans with (l' := -3 :: [2; 0; 8; 7]).
        { change [2; 0; -3; 8; 7] with ([2; 0] ++ -3 :: [8; 7]).
          apply Permutation_sym.
          apply Permutation_middle. }
        simpl. apply perm_skip.
        (* Goal: Permutation [2; 0; 8; 7] [0; 2; 7; 8] *)
        apply perm_swap.
        apply perm_skip.
        (* Goal: Permutation [2; 8; 7] [2; 7; 8] *)
        apply perm_skip.
        (* Goal: Permutation [8; 7] [7; 8] *)
        apply perm_swap.
        apply Permutation_refl.
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.