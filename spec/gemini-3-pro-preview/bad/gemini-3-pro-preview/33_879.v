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
  [10; 8; 7; 7; 5; 4; 3; 2; 1; 899; 0; -1; -2; -3; -4; -5; -6; -7; -8; -9; -10; -4] 
  [-8; 8; 7; -5; 5; 4; -4; 2; 1; -2; 0; -1; 3; -3; -4; 7; -6; -7; 10; -9; -10; 899].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; try tauto; try congruence | ]). apply NoDup_nil.
        -- repeat (constructor; [ simpl; try tauto; try congruence | ]). apply NoDup_nil.
        -- intros x. simpl. tauto.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; compute; congruence) ]).
        apply Sorted_nil.
Qed.