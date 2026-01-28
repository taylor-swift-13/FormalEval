Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    (forall r : R, In r input <-> In r Sorted_input) /\
    let len := length input in
    let halflen := (len / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen - 1) Sorted_input 0)) / 2).

Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.

Example example_list : list R := [3; 1; 2; 4; 5].
Example example_sorted : list R := [1; 2; 3; 4; 5].

Lemma example_sorted_sorted : Sorted Rle example_sorted.
Proof.
  repeat constructor; try (now apply Rle_refl).
Qed.

Lemma example_perm : Permutation example_list example_sorted.
Proof.
  repeat (try apply Permutation_refl).
  eapply Permutation_trans.
  - apply perm_swap.
  - eapply Permutation_trans.
    + apply perm_swap.
    + eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip.
        apply perm_swap.
Qed.

Lemma example_in_equiv : forall r,
    In r example_list <-> In r example_sorted.
Proof.
  intro r.
  rewrite <- (Permutation_in example_perm).
  reflexivity.
Qed.

Example example_median :
  problem_47_spec example_list 3.
Proof.
  unfold problem_47_spec.
  exists example_sorted.
  split.
  - apply example_sorted_sorted.
  - split.
    + apply example_in_equiv.
    + simpl.
      split.
      * intros _.
        reflexivity.
      * intros H.
        lia.
Qed.