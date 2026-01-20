Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Inductive Item :=
| IBool : bool -> Item
| IReal : R -> Item
| IString : string -> Item
| IListBool : list bool -> Item
| INone : Item.

Definition item_le (x y : Item) : Prop :=
  match x, y with
  | IBool b1, IBool b2 => (b1 = false \/ b2 = true)
  | _, _ => True
  end.

Fixpoint extract_thirds (l : list Item) (i : nat) : list Item :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Item) (res : list Item) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted item_le (extract_thirds res 0).

Definition input_list : list Item := [
  IBool false; 
  IReal (-99.72274847671751); 
  IString "FlYijS"; 
  IBool true; 
  IBool true; 
  IBool true; 
  IBool true; 
  IListBool [false; false]; 
  INone; 
  IBool false
].

Definition output_list : list Item := [
  IBool false; 
  IReal (-99.72274847671751); 
  IString "FlYijS"; 
  IBool false; 
  IBool true; 
  IBool true; 
  IBool true; 
  IListBool [false; false]; 
  INone; 
  IBool true
].

Example test_case : sort_third_spec input_list output_list.
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 11 (destruct i; [
        try (simpl in H; exfalso; apply H; reflexivity);
        try (simpl; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply perm_skip.
        transitivity [IBool true; IBool false; IBool true].
        apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; left; reflexivity) ]).
        apply Sorted_nil.
Qed.