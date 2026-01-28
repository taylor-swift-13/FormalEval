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
  [-4; 7; 3; -6; 3; 0; -8; 6; 2; 0; 12; 1; 8; 7] 
  [-8; 7; 3; -6; 3; 0; -4; 6; 2; 0; 12; 1; 8; 7].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 14 (destruct i; [ simpl in *; try reflexivity; try (exfalso; compute in H; congruence) | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        change [-8; -6; -4; 0; 8] with (([-8; -6; -4]) ++ [0; 8]).
        change [-4; -6; -8; 0; 8] with (([-4; -6; -8]) ++ [0; 8]).
        apply Permutation_app_tail.
        assert (Hrev: [-4; -6; -8] = rev [-8; -6; -4]) by reflexivity.
        rewrite Hrev.
        apply Permutation_rev.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; compute; discriminate ] ]).
        apply Sorted_nil.
Qed.