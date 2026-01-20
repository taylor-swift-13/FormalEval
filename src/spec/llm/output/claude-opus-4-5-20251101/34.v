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

(* Helper lemmas for the proof *)
Lemma is_sorted_concrete : is_sorted [0; 2; 3; 5; 9; 123].
Proof.
  unfold is_sorted.
  intros i j Hij Hj.
  simpl in Hj.
  destruct i as [|[|[|[|[|[|i']]]]]];
  destruct j as [|[|[|[|[|[|j']]]]]];
  simpl; try lia.
Qed.

Lemma no_dup_concrete : no_duplicates [0; 2; 3; 5; 9; 123].
Proof.
  unfold no_duplicates.
  repeat constructor; simpl; intuition; try discriminate.
Qed.

Lemma all_elements_concrete : all_elements_from [0; 2; 3; 5; 9; 123] [5; 3; 5; 2; 3; 3; 9; 0; 123].
Proof.
  unfold all_elements_from.
  intro x.
  simpl.
  split; intro H.
  - destruct H as [H|[H|[H|[H|[H|[H|H]]]]]]; subst; auto 10.
  - destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; subst; auto 10.
Qed.

Example unique_example : unique_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold unique_spec.
  split; [| split].
  - exact is_sorted_concrete.
  - exact no_dup_concrete.
  - exact all_elements_concrete.
Qed.