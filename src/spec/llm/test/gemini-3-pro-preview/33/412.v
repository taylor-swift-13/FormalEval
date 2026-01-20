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
  [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; -1; -2; -3; -4; 2; -5; -6; -7; -8; -9; -10] 
  [-8; 9; 8; -5; 6; 5; -3; 3; 2; 1; -1; -2; 4; -4; 2; 7; -6; -7; 10; -9; -10].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i as [|i]; [ simpl in H; try lia; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        assert (Hrev: [10; 7; 4; 1; -3; -5; -8] = rev [-8; -5; -3; 1; 4; 7; 10]) by reflexivity.
        rewrite Hrev.
        apply Permutation_rev.
      * simpl.
        repeat (constructor; simpl; try lia).
Qed.