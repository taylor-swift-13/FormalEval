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
  [-7; 6; 7; 290; 8; 289; 20; -4; 104; -277; 200; 3; 4; -8; 700; -2; -901; 800; 1000]
  [-277; 6; 7; -7; 8; 289; -2; -4; 104; 4; 200; 3; 20; -8; 700; 290; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_NoDup.
        -- repeat (constructor; [ intro H_in; simpl in H_in; repeat (destruct H_in as [H_eq | H_in]; [ discriminate H_eq | ]); try destruct H_in | ]).
        -- repeat (constructor; [ intro H_in; simpl in H_in; repeat (destruct H_in as [H_eq | H_in]; [ discriminate H_eq | ]); try destruct H_in | ]).
        -- intro x. split; intro H_in; simpl in H_in;
           repeat (destruct H_in as [H_eq | H_in]; [ rewrite H_eq; simpl; tauto | ]); try tauto.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try (vm_compute; exact I) ]).
        apply Sorted_nil.
Qed.