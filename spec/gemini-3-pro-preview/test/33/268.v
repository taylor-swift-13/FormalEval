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
  [9; -1; 700; -1; 6; -4; 3; 11; 3; -1] 
  [-1; -1; 700; -1; 6; -4; 3; 11; 3; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply Permutation_trans with (l' := -1 :: 9 :: 3 :: -1 :: []). constructor.
        apply perm_skip.
        apply Permutation_trans with (l' := 3 :: 9 :: -1 :: []). constructor.
        apply Permutation_trans with (l' := 3 :: -1 :: 9 :: []). apply perm_skip. constructor.
        constructor.
      * simpl.
        repeat constructor.
        -- unfold Z.le; simpl; discriminate.
        -- unfold Z.le; simpl; discriminate.
        -- unfold Z.le; simpl; discriminate.
Qed.