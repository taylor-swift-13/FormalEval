Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%R.

Example test_problem_35 : problem_35_spec [1.5; 3; -4; 2; -3.5; -1; 2] 3.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. right. left. reflexivity.
  - intros x Hx.
    simpl in Hx.
    destruct Hx as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | H8]]]]]]].
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + contradiction.
Qed.