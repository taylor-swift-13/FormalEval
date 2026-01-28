Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%R.

Example test_case_35 : problem_35_spec [1.2%R; -4.5%R; -3.4%R; 5.6%R; 15.4%R; -8.601314347821834%R; 10.1%R] 15.4%R.
Proof.
  unfold problem_35_spec.
  split.
  - simpl.
    right. right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + rewrite <- H; lra.
    + contradiction.
Qed.