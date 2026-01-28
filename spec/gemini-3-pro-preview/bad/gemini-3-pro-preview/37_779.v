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
  [5; 3; 10; -8; -5; 2; -3; -9; 0; 123; 1; -10; 10] 
  [-5; 3; -3; -8; 0; 2; 1; -9; 5; 123; 10; -10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* 1. Move -5 *)
        assert (H1: Permutation [5; 10; -5; -3; 0; 1; 10] ([5; 10] ++ -5 :: [-3; 0; 1; 10])) by reflexivity.
        rewrite H1.
        apply Permutation_trans with (l' := -5 :: ([5; 10] ++ [-3; 0; 1; 10])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* 2. Move -3 *)
        assert (H2: Permutation [5; 10; -3; 0; 1; 10] ([5; 10] ++ -3 :: [0; 1; 10])) by reflexivity.
        rewrite H2.
        apply Permutation_trans with (l' := -3 :: ([5; 10] ++ [0; 1; 10])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* 3. Move 0 *)
        assert (H3: Permutation [5; 10; 0; 1; 10] ([5; 10] ++ 0 :: [1; 10])) by reflexivity.
        rewrite H3.
        apply Permutation_trans with (l' := 0 :: ([5; 10] ++ [1; 10])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* 4. Move 1 *)
        assert (H4: Permutation [5; 10; 1; 10] ([5; 10] ++ 1 :: [10])) by reflexivity.
        rewrite H4.
        apply Permutation_trans with (l' := 1 :: ([5; 10] ++ [10])).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons. simpl.
        (* 5. Remaining elements are sorted *)
        repeat apply Permutation_cons.
        apply Permutation_nil.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.