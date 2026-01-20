Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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

Example test_case : sort_third_spec [1; 2; 3; -3; 5; 1; 0; -8; 9; -12; 7; 6; 6] 
                                    [-12; 2; 3; -3; 5; 1; 0; -8; 9; 1; 7; 6; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 13 (destruct i as [|i]; [
        simpl in H;
        try (exfalso; apply H; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_trans with (-12 :: [1; -3; 0; 6]).
        { apply Permutation_sym.
          change [1; -3; 0; -12; 6] with ([1; -3; 0] ++ -12 :: [6]).
          apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (-3 :: [1; 0; 6]).
        { apply Permutation_sym.
          change [1; -3; 0; 6] with ([1] ++ -3 :: [0; 6]).
          apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_trans with (0 :: [1; 6]).
        { apply Permutation_sym.
          change [1; 0; 6] with ([1] ++ 0 :: [6]).
          apply Permutation_middle. }
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat apply Sorted_cons.
        -- apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
        -- apply HdRel_cons. lia.
        -- apply HdRel_nil.
        -- apply Sorted_nil.
Qed.