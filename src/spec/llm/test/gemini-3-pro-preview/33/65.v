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
  [46; 32; 77; 22; 18; 57; 77; 88; 66; 54] 
  [22; 32; 77; 46; 18; 57; 54; 88; 66; 77].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 10 (destruct i; [ try (exfalso; apply H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        apply perm_trans with (l' := [22; 46; 77; 54]).
        -- apply perm_swap.
        -- apply perm_skip. apply perm_skip. apply perm_swap.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_nil.
                 --- apply HdRel_nil.
              ** apply HdRel_cons. compute. discriminate.
           ++ apply HdRel_cons. compute. discriminate.
        -- apply HdRel_cons. compute. discriminate.
Qed.