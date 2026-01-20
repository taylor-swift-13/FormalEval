Existing Coq output file content 
specification for the first test case `input = [[9%Z; 0%Z; 8%Z; -1%Z; 6%Z; -4%Z; -5%Z; 12%Z; 0%Z; -1%Z]], output = [-5%Z; 0%Z; 8%Z; -1%Z; 6%Z; -4%Z; -1%Z; 12%Z; 0%Z; 9%Z]`:
```coq
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
  [9; 0; 8; -1; 6; -4; -5; 12; 0; -1] 
  [-5; 0; 8; -1; 6; -4; -1; 12; 0; 9].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 10 (destruct i; [
        simpl in H; try congruence; simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply Permutation_trans.
        2: { apply Permutation_cons. apply Permutation_swap. }
        eapply Permutation_trans.
        2: { apply Permutation_swap. }
        apply Permutation_cons.
        eapply Permutation_trans.
        2: { apply Permutation_swap. }
        apply Permutation_cons.
        apply Permutation_swap.
      * simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons. compute. intro H. discriminate.
        -- apply HdRel_cons. compute. intro H. discriminate.
        -- apply HdRel_cons. compute. intro H. discriminate.
Qed.