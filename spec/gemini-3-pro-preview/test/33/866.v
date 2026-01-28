Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [9; 12; 3; 6; 15; 0; -3; -6; 18; 21; 30; -9; 0] 
  [-3; 12; 3; 0; 15; 0; 6; -6; 18; 9; 30; -9; 21].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        assert (H1: Permutation [9; 6; -3; 21; 0] (-3 :: [9; 6] ++ [21; 0])).
        { apply Permutation_sym. apply Permutation_middle. }
        rewrite H1. apply perm_skip. simpl.
        assert (H2: Permutation [9; 6; 21; 0] (0 :: [9; 6; 21] ++ [])).
        { apply Permutation_sym. apply Permutation_middle. }
        rewrite H2. apply perm_skip. simpl.
        assert (H3: Permutation [9; 6; 21] (6 :: [9] ++ [21])).
        { apply Permutation_sym. apply Permutation_middle. }
        rewrite H3. apply perm_skip. simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.