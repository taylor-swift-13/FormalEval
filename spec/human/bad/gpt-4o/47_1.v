Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Precondition: input must be non-empty to define median *)
Definition problem_47_pre (input : list R) : Prop := input <> [].

Definition problem_47_spec(input : list R) (output : R) : Prop :=
  exists Sorted_input,
    Sorted Rle Sorted_input /\
    (forall r : R, In r input <-> In r Sorted_input) /\
    let len := length input in
    let halflen := ((length input) / 2)%nat in
    ((len mod 2 = 1)%nat -> output = nth halflen Sorted_input 0) /\
    ((len mod 2 = 0)%nat -> output = ((nth halflen Sorted_input 0) + (nth (halflen-1) Sorted_input 0)) / 2).

Example median_test_case_1 :
  problem_47_spec [3; 1; 2; 4; 5] 3.
Proof.
  unfold problem_47_spec.
  exists [1; 2; 3; 4; 5].
  split.
  - repeat (constructor; auto with real).
  - split.
    + intros r. simpl. split; intro H; repeat (destruct H as [H | H]; subst; auto; try contradiction).
    + simpl. split.
      * intros H. simpl. reflexivity.
      * intros H. exfalso. apply Nat.mod_neq_0_1 in H. apply H. reflexivity.
Qed.