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
  [1; 1; 1; 1; 1; 1; -2; 2; 0; 2; 2; 0] 
  [-2; 1; 0; 1; 1; 1; 1; 2; 1; 2; 2; 0].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We destruct i repeatedly to handle each index. *)
      repeat (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      (* For i >= length, Hlen is contradictory *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 1; 1; -2; 0; 2] [-2; 0; 1; 1; 1; 2] *)
        
        (* Move -2 to front *)
        assert (H1: Permutation [1; 1; 1; -2; 0; 2] (-2 :: [1; 1; 1; 0; 2])).
        { change [1; 1; 1; -2; 0; 2] with ([1; 1; 1] ++ -2 :: [0; 2]).
          apply Permutation_sym, Permutation_middle. }
        rewrite H1; clear H1. apply perm_skip.
        
        (* Move 0 to front *)
        assert (H2: Permutation [1; 1; 1; 0; 2] (0 :: [1; 1; 1; 2])).
        { change [1; 1; 1; 0; 2] with ([1; 1; 1] ++ 0 :: [2]).
          apply Permutation_sym, Permutation_middle. }
        rewrite H2; clear H2. apply perm_skip.
        
        (* The remaining lists match *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.