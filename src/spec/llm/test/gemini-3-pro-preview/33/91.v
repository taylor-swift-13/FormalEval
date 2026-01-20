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

Example test_case : sort_third_spec [9; 12; 15; 6; 21; 8; 40; 26; 18; 12; 13] [6; 12; 15; 9; 21; 8; 12; 26; 18; 40; 13].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [ simpl in H |- *; try lia; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := [6; 9; 40; 12]).
        -- apply perm_skip. apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
        -- simpl. apply HdRel_cons. lia.
Qed.