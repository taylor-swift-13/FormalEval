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

Definition is_sorted_R (l : list R) : Prop :=
  forall i j, (i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 <= nth j l 0.

Definition no_duplicates_R (l : list R) : Prop :=
  NoDup l.

Definition all_elements_from_R (result original : list R) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec_R (l : list R) (result : list R) : Prop :=
  is_sorted_R result /\
  no_duplicates_R result /\
  all_elements_from_R result l.

Lemma is_sorted_concrete : is_sorted_R [1.1; 2.2; 3.3; 4.4].
Proof.
  unfold is_sorted_R.
  intros i j Hij Hj.
  simpl in Hj.
  destruct i as [|[|[|[|i']]]];
  destruct j as [|[|[|[|j']]]];
  simpl; try lia; try lra.
Qed.

Lemma no_dup_concrete : no_duplicates_R [1.1; 2.2; 3.3; 4.4].
Proof.
  unfold no_duplicates_R.
  repeat constructor; simpl; intuition; try lra.
Qed.

Lemma all_elements_concrete : all_elements_from_R [1.1; 2.2; 3.3; 4.4] [1.1; 2.2; 3.3; 4.4; 4.4; 2.2; 1.1].
Proof.
  unfold all_elements_from_R.
  intro x.
  simpl.
  split; intro H.
  - destruct H as [H|[H|[H|[H|H]]]]; subst; auto 10.
  - destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; auto 10.
Qed.

Example unique_example : unique_spec_R [1.1; 2.2; 3.3; 4.4; 4.4; 2.2; 1.1] [1.1; 2.2; 3.3; 4.4].
Proof.
  unfold unique_spec_R.
  split; [| split].
  - exact is_sorted_concrete.
  - exact no_dup_concrete.
  - exact all_elements_concrete.
Qed.