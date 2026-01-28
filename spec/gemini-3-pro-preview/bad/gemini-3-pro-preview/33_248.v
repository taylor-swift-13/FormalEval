Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [1; 1; 2; 3; 5; 1; 0; -8; 9; 0; -12; 7; 6; 6; 1; -12; 1] 
  [-12; 1; 2; 0; 5; 1; 0; -8; 9; 1; -12; 7; 3; 6; 1; 6; 1].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ simpl in *; try (elim H; discriminate); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        assert (H1: Permutation [1; 3; 0; 0; 6; -12] (-12 :: [1; 3; 0; 0; 6])).
        { apply Permutation_sym, Permutation_middle. }
        rewrite H1. apply Permutation_cons.
        assert (H2: Permutation (1 :: 3 :: 0 :: 0 :: 6 :: nil) (0 :: 1 :: 3 :: 0 :: 6 :: nil)).
        { change (1 :: 3 :: 0 :: 0 :: 6 :: nil) with ([1; 3] ++ 0 :: [0; 6]). apply Permutation_sym, Permutation_middle. }
        rewrite H2. apply Permutation_cons.
        assert (H3: Permutation (1 :: 3 :: 0 :: 6 :: nil) (0 :: 1 :: 3 :: 6 :: nil)).
        { change (1 :: 3 :: 0 :: 6 :: nil) with ([1; 3] ++ 0 :: [6]). apply Permutation_sym, Permutation_middle. }
        rewrite H3. apply Permutation_cons.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply Zle_bool_imp_le; vm_compute; reflexivity | ]).
        apply Sorted_nil.
Qed.