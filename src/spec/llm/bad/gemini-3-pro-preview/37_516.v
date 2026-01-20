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
  [-7; 2; 3; 5; 7; 10; 5; 10; -7; 7; 2] 
  [-7; 2; -7; 5; 2; 10; 3; 10; 5; 7; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in *; try discriminate; simpl; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply perm_skip.
        assert (H1: Permutation [3; 7; 5; -7; 2] (-7 :: [3; 7; 5; 2])).
        { change [3; 7; 5; -7; 2] with ([3; 7; 5] ++ -7 :: [2]). 
          apply Permutation_cons_app. apply Permutation_refl. }
        apply (Permutation_trans H1). clear H1.
        apply perm_skip.
        assert (H2: Permutation [3; 7; 5; 2] (2 :: [3; 7; 5])).
        { change [3; 7; 5; 2] with ([3; 7; 5] ++ 2 :: []).
          apply Permutation_cons_app. apply Permutation_refl. }
        apply (Permutation_trans H2). clear H2.
        apply perm_skip.
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.