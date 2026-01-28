Existing Coq output file content 
specification for the first test case `input = [[1%Z; 2%Z; 3%Z; 5%Z; 1%Z; 16%Z; 16%Z; -8%Z; 9%Z; -12%Z; 7%Z; 4%Z; 6%Z; -12%Z; 16%Z]], output = [-12%Z; 2%Z; 3%Z; 1%Z; 1%Z; 16%Z; 5%Z; -8%Z; 9%Z; 6%Z; 7%Z; 4%Z; 16%Z; -12%Z; 16%Z]`:
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
  [1; 2; 3; 5; 1; 16; 16; -8; 9; -12; 7; 4; 6; -12; 16] 
  [-12; 2; 3; 1; 1; 16; 5; -8; 9; 6; 7; 4; 16; -12; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 16 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_trans with (l' := -12 :: [1; 5; 16] ++ [6]).
        -- simpl. apply perm_skip. apply perm_skip. apply perm_skip.
           apply perm_swap.
        -- change [1; 5; 16; -12; 6] with ([1; 5; 16] ++ -12 :: [6]).
           apply Permutation_middle.
      * simpl.
        repeat constructor; unfold Z.le; simpl; intro Hc; discriminate.
Qed.