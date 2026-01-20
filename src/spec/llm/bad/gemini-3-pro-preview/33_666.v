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

Ltac solve_add :=
  match goal with
  | [ |- Add ?x ?l (?x :: ?r) ] =>
      apply Add_head
  | [ |- Add ?x ?l (?y :: ?r) ] =>
      apply Add_cons; solve_add
  end.

Ltac solve_perm :=
  match goal with
  | [ |- Permutation [] [] ] => apply Permutation_refl
  | [ |- Permutation (?x :: ?l) ?r ] =>
      apply Permutation_Add;
      eexists; split; [ solve_add | solve_perm ]
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800]
  [-901; 500; 6; 4; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; -200; -104; 900; 800].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i as [|i]; [
        simpl; try reflexivity; try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. solve_perm.
      * simpl.
        repeat (apply Sorted_cons || apply HdRel_cons || apply HdRel_nil);
        try (apply Z.leb_le; reflexivity).
Qed.