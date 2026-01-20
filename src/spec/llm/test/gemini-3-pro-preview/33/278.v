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
  [2; 3; -3; 1; 16; 16; -8; 9; -12; 7; 6; -12; 16; 7] 
  [-8; 3; -3; 1; 16; 16; 2; 9; -12; 7; 6; -12; 16; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try reflexivity; try (elim H; reflexivity) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans.
        2: apply perm_swap.
        eapply Permutation_trans.
        2: apply perm_skip; apply perm_swap.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; apply HdRel_cons; cbv; intro Hc; discriminate]).
        apply Sorted_nil.
Qed.