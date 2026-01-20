Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import String.

Import ListNotations.

Definition is_sorted (l : list string) : Prop :=
  forall i j, i < j -> j < length l -> 
    String.leb (nth i l EmptyString) (nth j l EmptyString) = true.

Definition no_duplicates (l : list string) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list string) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list string) (result : list string) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Lemma is_sorted_concrete : is_sorted ["apple"; "banana"; "olQdrange"].
Proof.
  unfold is_sorted.
  intros i j Hij Hj.
  simpl in Hj.
  destruct i as [|[|[|i']]];
  destruct j as [|[|[|j']]];
  simpl; try lia; try reflexivity.
Qed.

Lemma no_dup_concrete : no_duplicates ["apple"; "banana"; "olQdrange"].
Proof.
  unfold no_duplicates.
  repeat constructor; simpl; intuition; try discriminate.
Qed.

Lemma all_elements_concrete : all_elements_from ["apple"; "banana"; "olQdrange"] ["apple"; "banana"; "olQdrange"].
Proof.
  unfold all_elements_from.
  intro x.
  simpl.
  split; intro H; exact H.
Qed.

Example unique_example : unique_spec ["apple"; "banana"; "olQdrange"] ["apple"; "banana"; "olQdrange"].
Proof.
  unfold unique_spec.
  split; [| split].
  - exact is_sorted_concrete.
  - exact no_dup_concrete.
  - exact all_elements_concrete.
Qed.