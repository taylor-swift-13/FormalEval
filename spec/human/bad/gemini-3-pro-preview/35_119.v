Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> x <= output.

Example test_case_35 : problem_35_spec [1.2%R; -4.5%R; -3.4%R; 5.6%R; 30.7%R; 7.8%R; -9.0%R; 10.1%R; 1.2%R] 30.7%R.
Proof.
  unfold problem_35_spec.
  split.
  - simpl.
    do 4 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat destruct H as [H|H]; try lra.
    contradiction.
Qed.