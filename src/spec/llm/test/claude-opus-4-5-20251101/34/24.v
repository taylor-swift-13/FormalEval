Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import Reals.
Require Import Lra.

Import ListNotations.

Open Scope R_scope.

Definition is_sorted (l : list R) : Prop :=
  forall i j, (i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 <= nth j l 0.

Definition no_duplicates (l : list R) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list R) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list R) (result : list R) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Lemma is_sorted_concrete : is_sorted [1.1; 2.2; 3.0219968583931567; 4.4].
Proof.
  unfold is_sorted.
  intros i j Hij Hj.
  simpl in Hj.
  destruct i as [|[|[|[|i']]]];
  destruct j as [|[|[|[|j']]]];
  simpl; try lia; try lra.
Qed.

Lemma no_dup_concrete : no_duplicates [1.1; 2.2; 3.0219968583931567; 4.4].
Proof.
  unfold no_duplicates.
  repeat constructor; simpl; intuition; try lra.
Qed.

Lemma all_elements_concrete : all_elements_from [1.1; 2.2; 3.0219968583931567; 4.4] [3.0219968583931567; 1.1; 2.2; 4.4; 4.4].
Proof.
  unfold all_elements_from.
  intro x.
  simpl.
  split; intro H.
  - destruct H as [H|[H|[H|[H|H]]]]; subst; auto 10.
  - destruct H as [H|[H|[H|[H|[H|H]]]]]; subst; auto 10.
Qed.

Example unique_example : unique_spec [3.0219968583931567; 1.1; 2.2; 4.4; 4.4] [1.1; 2.2; 3.0219968583931567; 4.4].
Proof.
  unfold unique_spec.
  split; [| split].
  - exact is_sorted_concrete.
  - exact no_dup_concrete.
  - exact all_elements_concrete.
Qed.