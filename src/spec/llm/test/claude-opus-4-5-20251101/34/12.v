Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.
Require Import Bool.

Import ListNotations.

Definition is_sorted (l : list bool) : Prop :=
  forall i j, i < j -> j < length l -> 
    negb (nth i l false) || nth j l false = true.

Definition no_duplicates (l : list bool) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list bool) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list bool) (result : list bool) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Lemma is_sorted_concrete : is_sorted [true].
Proof.
  unfold is_sorted.
  intros i j Hij Hj.
  simpl in Hj.
  lia.
Qed.

Lemma no_dup_concrete : no_duplicates [true].
Proof.
  unfold no_duplicates.
  constructor.
  - simpl. auto.
  - constructor.
Qed.

Lemma all_elements_concrete : all_elements_from [true] [true].
Proof.
  unfold all_elements_from.
  intro x.
  simpl.
  split; intro H; auto.
Qed.

Example unique_example : unique_spec [true] [true].
Proof.
  unfold unique_spec.
  split; [| split].
  - exact is_sorted_concrete.
  - exact no_dup_concrete.
  - exact all_elements_concrete.
Qed.