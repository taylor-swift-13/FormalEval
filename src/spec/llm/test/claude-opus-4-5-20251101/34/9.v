Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.
Require Import Bool.

Import ListNotations.

Definition is_sorted (l : list nat) : Prop :=
  forall i j, i < j -> j < length l -> 
    nth i l 0 <= nth j l 0.

Definition no_duplicates (l : list nat) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list nat) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list nat) (result : list nat) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Lemma is_sorted_empty : is_sorted [].
Proof.
  unfold is_sorted.
  intros i j Hij Hj.
  simpl in Hj.
  lia.
Qed.

Lemma no_dup_empty : no_duplicates [].
Proof.
  unfold no_duplicates.
  constructor.
Qed.

Lemma all_elements_empty : all_elements_from [] [].
Proof.
  unfold all_elements_from.
  intro x.
  simpl.
  split; intro H; exact H.
Qed.

Example unique_example : unique_spec [] [].
Proof.
  unfold unique_spec.
  split; [| split].
  - exact is_sorted_empty.
  - exact no_dup_empty.
  - exact all_elements_empty.
Qed.