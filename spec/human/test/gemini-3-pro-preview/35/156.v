Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%R.

Example test_case_35 : problem_35_spec [1.2%R; -3.4%R; 1.2%R; -3.4%R; 5.6%R; 17.742268880987826%R; -9.0%R; 10.1%R] 17.742268880987826%R.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; try lra; try contradiction.
Qed.