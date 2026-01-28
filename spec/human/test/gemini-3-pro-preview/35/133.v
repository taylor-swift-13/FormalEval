Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> x <= output.

Example test_case_35 : problem_35_spec [1.2; 1.3749746958929525; -4.5; -3.4; 5.6; 7.8; -9.0; 10.1; 1.2] 10.1.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
Qed.