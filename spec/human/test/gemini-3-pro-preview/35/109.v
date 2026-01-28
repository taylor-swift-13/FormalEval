Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope R_scope.

Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> x <= output.

Example test_case_35 : problem_35_spec [1.2; -4.5; -3.4; 5.6; 15.4; -9.0; 10.1] 15.4.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + rewrite <- H. lra.
    + contradiction.
Qed.