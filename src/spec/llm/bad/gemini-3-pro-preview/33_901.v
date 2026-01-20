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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1; -6] 
  [-11; 9; 8; -7; 6; 5; -6; 2; 1; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 500].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ 
        try (compute in H; congruence); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        repeat (
          match goal with
          | [ |- Permutation (?a :: ?l) ?r ] =>
            eapply Permutation_trans with (l' := a :: _);
            [ apply Permutation_cons | 
              apply Permutation_Add; solve [ repeat (constructor || apply Add_cons) ] ]
          end
        ).
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; apply Z.leb_le; reflexivity ]).
        apply Sorted_nil.
Qed.